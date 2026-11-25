/*
 * TXID / Address -> RFC 6979 deterministic-nonce COLLISION detector + key recovery.
 * Engine extracted from the CryptographyTube Tools collection.
 * Self-contained: depends only on CryptoJS (crypto-js) which is loaded
 * before this file. Exposes window.processTxid() and window.exportOne().
 *
 * RFC 6979 makes the ECDSA nonce deterministic: k = HMAC_DRBG(d, H(m)). For a
 * fixed key d, two DIFFERENT messages must yield DIFFERENT k (because H(m)
 * differs). A broken implementation (truncated HMAC state, wrong hash input,
 * reused DRBG output, 32-bit counter, etc.) can emit the SAME k for two
 * different messages under one key. That shows up on-chain as the same r for
 * two signatures of the same public key but with different z. When it happens,
 * the private key falls out in closed form:
 *
 *     k = (z1 - z2) / (s1 - s2)  mod n
 *     d = (s1*k - z1) / r        mod n
 *
 * This tool groups a key's signatures, flags any r that repeats across
 * different z (a genuine RFC 6979 determinism failure — not just an identical
 * re-broadcast), recovers d, and ACCEPTS it only when d*G reproduces the
 * on-chain public key. 100% client-side, verified — no false positives.
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

    // ---- Hashing (CryptoJS) ---------------------------------------------
    function sha256hex(hex) { return CryptoJS.SHA256(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function ripe160hex(hex) { return CryptoJS.RIPEMD160(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function dblsha256(hex) { return sha256hex(sha256hex(hex)); }

    // ---- secp256k1 math (main thread — verification of recovered d) ------
    const P_CURVE = (2n ** 256n) - (2n ** 32n) - 977n;
    const Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n;
    const Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8n;

    function mod(a, m) { var r = a % m; return r < 0n ? r + m : r; }
    function egcd(a, b) { if (b === 0n) return [a, 1n, 0n]; var r = egcd(b, a % b); return [r[0], r[2], r[1] - (a / b) * r[2]]; }
    function modInv(a, m) { a = mod(a, m); var r = egcd(a, m); if (r[0] !== 1n) throw new Error("no inverse"); return mod(r[1], m); }
    function ptAdd(Pp, Qp) {
        if (!Pp) return Qp; if (!Qp) return Pp;
        if (Pp.x === Qp.x && mod(Pp.y + Qp.y, P_CURVE) === 0n) return null;
        var l;
        if (Pp.x === Qp.x && Pp.y === Qp.y) { l = mod((3n * Pp.x * Pp.x) * modInv(2n * Pp.y, P_CURVE), P_CURVE); }
        else { l = mod((Qp.y - Pp.y) * modInv(mod(Qp.x - Pp.x, P_CURVE), P_CURVE), P_CURVE); }
        var x = mod(l * l - Pp.x - Qp.x, P_CURVE);
        var y = mod(l * (Pp.x - x) - Pp.y, P_CURVE);
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
            var y = BigInt("0x" + pub.slice(66));
            return (y & 1n ? "03" : "02") + pub.slice(2, 66);
        }
        return null;
    }

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

    // Private key (BigInt) -> WIF (compressed).
    function privToWif(d) {
        var pk = hx(d);
        var payload = "80" + pk + "01";
        var checksum = dblsha256(payload).substring(0, 8);
        return b58encode(payload + checksum);
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

            if (inp.script_hex) {
                const sigData = parseScriptSig(inp.script_hex);
                if (sigData.r) { r = sigData.r; s = sigData.s; pub = sigData.pub; }
            }

            if (!r && inp.witness && inp.witness.length >= 2) {
                const witnessSig = inp.witness[0];
                const witnessPub = inp.witness[1];
                if (witnessSig && witnessPub) {
                    const der = parseDER(witnessSig);
                    if (der.r) { r = der.r; s = der.s; pub = witnessPub; }
                }
            }

            if (!r || !s || !pub) continue;

            const addr = pubToAddr_P2PKH(pub);
            let z = "";
            try {
                const pubHash160 = ripe160hex(sha256hex(pub));
                const scriptPubKey = "76a914" + pubHash160 + "88ac";
                z = getrsz_v2(parsed, i, scriptPubKey);
            } catch (e) { z = ""; }

            results.push({ input_index: i, addr: addr, r: r, s: s, z: z, pub: pub });
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

    async function fetchAddressTxids(addr, want, onProgress) {
        let anyOk = false;

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
                if (arr.length < 25) break;
                await new Promise(r => setTimeout(r, 120));
            }
            if (txids.length > 0) return txids.slice(0, want);
            if (anyOk) return [];
        } catch (e) { /* fall through */ }

        try {
            let txids = [];
            let total = null;
            let offset = 0;
            const PAGE = 50;
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

        const txHashes = await fetchAddressTxids(addr, want, onProgress);
        if (txHashes === null) {
            throw new Error("Couldn't reach a block explorer for this address (it may be rate-limiting). Please wait a few seconds and try again, or lower the count.");
        }
        if (txHashes.length === 0) return results;

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

    // ---- Address balance / activity stats --------------------------------
    function formatBtc(sats) {
        const n = Number(sats || 0) / 1e8;
        const s = n.toFixed(8).replace(/\.?0+$/, '');
        return (s || '0') + ' BTC';
    }

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

    // ---- Output header + export ------------------------------------------
    function getOutputHeader(elementId) {
        let header = `<div class="result-header">CRYPTOGRAPHYTUBE<span class="tool-tag">RFC 6979 Deterministic-Nonce Collision</span></div>`;
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

    // ---- RFC 6979 collision detection + key recovery ---------------------
    // Group by public key, then index each key's signatures by r. A key that
    // signs two DIFFERENT messages (z1 != z2) with the SAME r reused the same
    // nonce k — an RFC 6979 determinism failure. Recover and verify.
    function detectCollisions(rsz) {
        // group by pubkey
        var byPub = Object.create(null);
        for (var i = 0; i < rsz.length; i++) {
            var e = rsz[i];
            if (!e.r || !e.s || !e.z || !e.pub) continue;
            var pk = e.pub.toLowerCase();
            (byPub[pk] || (byPub[pk] = [])).push(e);
        }

        var clusters = [];
        Object.keys(byPub).forEach(function (pk) {
            var sigs = byPub[pk];
            // index this key's sigs by r
            var byR = Object.create(null);
            for (var i = 0; i < sigs.length; i++) {
                var rk = sigs[i].r.toLowerCase();
                (byR[rk] || (byR[rk] = [])).push(sigs[i]);
            }
            Object.keys(byR).forEach(function (rk) {
                var members = byR[rk];
                if (members.length < 2) return;   // r must repeat

                // Find a pair with DIFFERENT z (true RFC 6979 failure, not a
                // duplicate broadcast of the very same signature).
                var pair = null;
                for (var a = 0; a < members.length && !pair; a++) {
                    for (var b = a + 1; b < members.length; b++) {
                        var za = members[a].z.toLowerCase(), zb = members[b].z.toLowerCase();
                        if (za !== zb) { pair = [members[a], members[b]]; break; }
                    }
                }
                if (!pair) return;   // same r but identical z -> just a rebroadcast

                var recovered = recoverFromPair(pair[0], pair[1], members[0].pub);
                if (!recovered) return;   // did not verify against the on-chain key

                clusters.push({
                    pub: members[0].pub,
                    addr: members[0].addr,
                    r: rk,
                    k: recovered.k,
                    priv: recovered.priv,
                    wif: recovered.wif,
                    sigCount: members.length,
                    members: members,
                    pair: pair
                });
            });
        });
        return clusters;
    }

    // k = (z1 - z2)/(s1 - s2); d = (s1*k - z1)/r ; accept iff d*G == pub.
    // Also tries the negated-nonce variants so an implementation that emitted
    // (r, -k) on one message still resolves.
    function recoverFromPair(A, B, pubHex) {
        try {
            var r = BigInt("0x" + A.r);
            var s1 = BigInt("0x" + A.s), z1 = BigInt("0x" + A.z);
            var s2 = BigInt("0x" + B.s), z2 = BigInt("0x" + B.z);
            if (r === 0n) return null;
            var cpub = compressPub(pubHex);
            if (!cpub) return null;
            var rInv = modInv(r, N);
            var dz = mod(z1 - z2, N);

            var kCands = [];
            var dsm = mod(s1 - s2, N);
            if (dsm !== 0n) kCands.push(mod(dz * modInv(dsm, N), N));   // same k
            var dsp = mod(s1 + s2, N);
            if (dsp !== 0n) kCands.push(mod(dz * modInv(dsp, N), N));   // one nonce negated

            for (var i = 0; i < kCands.length; i++) {
                var k = kCands[i];
                if (k <= 0n || k >= N) continue;
                var dCands = [
                    mod(mod(s1 * k - z1, N) * rInv, N),
                    mod(mod(mod(-s1, N) * k - z1, N) * rInv, N)
                ];
                for (var j = 0; j < dCands.length; j++) {
                    var d = dCands[j];
                    if (d <= 0n || d >= N) continue;
                    var Q = sMul(d);
                    if (Q && compressPoint(Q) === cpub) {
                        return { k: hx(k), priv: hx(d), wif: privToWif(d) };
                    }
                }
            }
        } catch (e) { /* not solvable */ }
        return null;
    }

    // ---- Result rendering ------------------------------------------------
    function renderResults(rsz, input, mode, stats) {
        const total = rsz ? rsz.length : 0;
        if (!total) {
            return '<div class="rsz-status rsz-empty">No ECDSA signatures were found for this ' +
                (mode === 'txid' ? 'transaction' : 'address') + '.</div>';
        }

        const clusters = detectCollisions(rsz);

        let html = '';
        html += '<div class="rsz-leak-box">';
        if (clusters.length) {
            let sigTotal = 0;
            clusters.forEach(function (c) { sigTotal += c.sigCount; });
            html += '<div class="rsz-summary">';
            html += '<span class="rsz-chip rsz-chip-danger">' + clusters.length + ' RFC 6979 collision' + (clusters.length > 1 ? 's' : '') + '</span>';
            html += '<span class="rsz-chip rsz-chip-danger">Private key recovered</span>';
            html += '<span class="rsz-chip">' + total + ' signatures scanned</span>';
            html += '</div>';
            html += '<div class="rsz-leak-note"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' +
                '<span>The same nonce <strong>k</strong> (same <strong>r</strong>) was used to sign <strong>different messages</strong> under one key &mdash; ' +
                'a broken RFC 6979 deterministic-nonce implementation. The private key is recovered in closed form ' +
                'from <strong>k = (z1&minus;z2)/(s1&minus;s2)</strong>, <strong>d = (s1&middot;k&minus;z1)/r</strong>, and verified against the on-chain public key.</span></div>';
        } else {
            html += '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">No RFC 6979 collision</span>' +
                '<span class="rsz-chip">' + total + ' signatures scanned</span></div>';
            html += '<div class="rsz-leak-note rsz-leak-ok"><img src="../assets/svgs/solid/circle-check.svg" width="14" height="14" alt=""> ' +
                '<span>Every signature from each key uses a distinct nonce for a distinct message &mdash; no repeated <strong>r</strong> across different <strong>z</strong>. ' +
                'RFC 6979 determinism is intact here and no key can be recovered by this method.</span></div>';
        }
        html += '</div>';

        // Recovered-key panels
        for (let ci = 0; ci < clusters.length; ci++) {
            const c = clusters[ci];
            html += '<div class="rsz-vuln-box">';
            html += '<div class="rsz-vuln-title"><img src="../assets/svgs/solid/key.svg" width="15" height="15" alt=""> Recovered private key &mdash; ' + escapeHtml(c.addr) + '</div>';
            html += '<div class="rsz-vuln-key"><span class="key-label">PRIV (hex)</span><code class="rsz-val private-key">' + escapeHtml(c.priv) + '</code>' + copyBtn(c.priv) + '</div>';
            html += '<div class="rsz-vuln-key"><span class="key-label">WIF</span><code class="rsz-val private-key">' + escapeHtml(c.wif) + '</code>' + copyBtn(c.wif) + '</div>';
            html += '<div class="rsz-vuln-key"><span class="key-label">NONCE k</span><code class="rsz-val rsz-nonce">' + escapeHtml(c.k) + '</code>' + copyBtn(c.k) + '</div>';
            html += rszLine('SHARED r', c.r);
            html += addrLine('ADDRESS', c.addr);
            html += rszLine('PUBKEY', c.pub);
            html += '</div>';
        }

        // Per-signature table
        html += '<div class="rsz-thead">';
        html += '<div><img src="../assets/svgs/solid/hashtag.svg" width="13" height="13" alt=""> Transaction / Address</div>';
        html += '<div><img src="../assets/svgs/solid/calculator.svg" width="13" height="13" alt=""> R &middot; S &middot; Z</div>';
        html += '<div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> Nonce Status</div>';
        html += '</div>';

        // mark which (r under a pub) collided
        const collidedR = Object.create(null);
        clusters.forEach(function (c) { collidedR[(c.pub + '|' + c.r).toLowerCase()] = c; });

        for (let idx = 0; idx < rsz.length; idx++) {
            const e = rsz[idx];
            const hit = e.pub ? collidedR[(e.pub + '|' + (e.r || '').toLowerCase())] : null;
            html += '<div class="rsz-row' + (hit ? ' rsz-row-vuln' : '') + '">';
            html += '<div class="rsz-col rsz-col-txid">' +
                (e.txid ? ('<span class="key-label">TXID</span>' + monoCell(e.txid, 'rsz-txid')) :
                    ('<span class="key-label">INPUT</span>' + monoCell('#' + e.input_index))) +
                addrLine('ADDR', e.addr) + '</div>';
            html += '<div class="rsz-col rsz-col-rsz">' + rszLine('R', e.r) + rszLine('S', e.s) + rszLine('Z', e.z) + '</div>';
            html += '<div class="rsz-col rsz-col-addr">';
            if (hit) {
                html += '<div class="rsz-line"><span class="rsz-tag">k</span><span class="rsz-chip rsz-chip-danger">REUSED &middot; RECOVERED</span></div>';
                html += '<div class="rsz-line"><span class="rsz-tag">PRIV</span><code class="rsz-val private-key">' + escapeHtml(hit.priv) + '</code>' + copyBtn(hit.priv) + '</div>';
            } else {
                html += '<div class="rsz-line"><span class="rsz-tag">k</span><span class="rsz-chip rsz-chip-ok">UNIQUE</span></div>';
            }
            html += '</div>';
            html += '</div>';
        }

        return html;
    }

    // ---- Main entry ------------------------------------------------------
    async function processTxid() {
        const input = document.getElementById("txid_input").value.trim();
        const out = document.getElementById("out_txid");
        if (!input) return;

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
                setStatus('Extracting R·S·Z signatures… ' + p.scanned + ' / ' + p.target + '  (signatures: ' + p.found + ')');
            }
        };

        setStatus('Analyzing input (TXID or Address)…');

        try {
            let rsz = [];
            let mode = "";
            let stats = null;
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
                try { stats = await fetchAddressStats(input); setStats(stats); } catch (e) { setStats(null); }
                rsz = await resolveInputToRSZ(input, want, onProgress);
            } else {
                throw new Error("Invalid input. Paste a 64-character TXID or a Bitcoin address.");
            }

            out.innerHTML = header + renderResults(rsz, input, mode, stats);
        } catch (e) {
            out.innerHTML = header +
                '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Error: ' +
                escapeHtml(e.message) + '</div>';
        }
    }

    async function resolveInputToRSZ(input, want, onProgress) {
        if (!input) return [];
        let inText = input.trim();
        if (inText.length >= 26 && inText.length <= 62 && !inText.includes(':')) {
            return await fetchBlockchainData(inText, want, onProgress);
        }
        return [];
    }

    // ---- Expose globals used by inline onclick handlers ------------------
    window.processTxid = processTxid;
    window.exportOne = exportOne;
})();

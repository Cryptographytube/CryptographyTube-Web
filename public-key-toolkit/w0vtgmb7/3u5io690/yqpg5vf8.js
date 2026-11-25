/*
 * Public Key Toolkit — X/Y, HASH160 & every Bitcoin address type.
 * Self-contained: depends only on CryptoJS (loaded before this file).
 * Exposes window.PublicKeyToolkit.analyze() and window.exportOne().
 *
 * Input (auto-detected):
 *   • Public key   — compressed (02/03 + 64 hex) or uncompressed (04 + 128 hex)
 *   • HASH160      — 40 hex characters (RIPEMD-160 of a public key)
 *   • Address      — legacy P2PKH (1…), P2SH (3…) or native SegWit (bc1…)
 *
 * For an address, the public key is recovered by scanning its spending
 * transactions for the key it revealed on-chain (blockstream.info, with
 * blockchain.info as a fallback). All key math runs locally in the browser.
 */
(function () {
    "use strict";

    // ---- Constants -------------------------------------------------------
    const B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    const BECH32_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l";
    // secp256k1 field prime (p = 2^256 - 2^32 - 977; p % 4 == 3)
    const P = BigInt('0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F');

    // ---- Low-level converters -------------------------------------------
    function hexToBytes(hex) {
        if (!hex || typeof hex !== 'string') return new Uint8Array();
        hex = hex.replace(/^0x/i, '');
        if (hex.length % 2 !== 0) hex = '0' + hex;
        const m = hex.match(/.{1,2}/g);
        return m ? new Uint8Array(m.map(b => parseInt(b, 16))) : new Uint8Array();
    }
    function bytesToHex(bytes) {
        return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
    }

    // ---- Hashing (CryptoJS) ---------------------------------------------
    function sha256hex(hex) { return CryptoJS.SHA256(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function ripe160hex(hex) { return CryptoJS.RIPEMD160(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function hash160hex(hex) { return ripe160hex(sha256hex(hex)); }

    // ---- secp256k1 point decompression ----------------------------------
    function modpow(base, exp, mod) {
        base %= mod; let r = 1n;
        while (exp > 0n) { if (exp & 1n) r = (r * base) % mod; exp >>= 1n; base = (base * base) % mod; }
        return r;
    }
    // Decompress a compressed pubkey hex (02/03 + 64 hex) -> { x, y } BigInts.
    function decompress(compressedHex) {
        const prefix = compressedHex.slice(0, 2);
        const x = BigInt('0x' + compressedHex.slice(2));
        if (x <= 0n || x >= P) throw new Error("Public key X is out of range.");
        const ySq = (modpow(x, 3n, P) + 7n) % P;
        let y = modpow(ySq, (P + 1n) / 4n, P);
        // Confirm the point is actually on the curve.
        if ((y * y) % P !== ySq) throw new Error("Invalid public key (point is not on the secp256k1 curve).");
        const wantOdd = prefix === '03';
        if ((y & 1n) !== (wantOdd ? 1n : 0n)) y = P - y;
        return { x, y };
    }
    const to64 = (n) => n.toString(16).padStart(64, '0');
    function compressPoint(x, y) { return ((y & 1n) ? '03' : '02') + to64(x); }
    function uncompressPoint(x, y) { return '04' + to64(x) + to64(y); }

    // Parse any pubkey hex -> { x, y, compressed, uncompressed }.
    function parsePubkey(hex) {
        hex = hex.toLowerCase();
        if (/^0[23][0-9a-f]{64}$/.test(hex)) {
            const { x, y } = decompress(hex);
            return { x, y, compressed: hex, uncompressed: uncompressPoint(x, y) };
        }
        if (/^04[0-9a-f]{128}$/.test(hex)) {
            const x = BigInt('0x' + hex.slice(2, 66));
            const y = BigInt('0x' + hex.slice(66));
            if (x >= P || y >= P) throw new Error("Public key coordinate out of range.");
            if ((y * y) % P !== (modpow(x, 3n, P) + 7n) % P)
                throw new Error("Invalid public key (point is not on the secp256k1 curve).");
            return { x, y, compressed: compressPoint(x, y), uncompressed: hex };
        }
        throw new Error("Not a valid public key.");
    }

    // ---- Base58 / Base58Check -------------------------------------------
    function b58encode(bytes) {
        let num = 0n;
        for (const b of bytes) num = num * 256n + BigInt(b);
        let str = "";
        while (num > 0n) { str = B58[Number(num % 58n)] + str; num /= 58n; }
        for (const b of bytes) { if (b === 0) str = "1" + str; else break; }
        return str || "1";
    }
    function b58decode(str) {
        let num = 0n;
        for (const ch of str) {
            const v = B58.indexOf(ch);
            if (v < 0) throw new Error("Invalid Base58 character.");
            num = num * 58n + BigInt(v);
        }
        let hex = num.toString(16);
        if (hex.length % 2) hex = '0' + hex;
        let bytes = Array.from(hexToBytes(hex));
        for (const ch of str) { if (ch === '1') bytes.unshift(0); else break; }
        return new Uint8Array(bytes);
    }
    // base58check from version byte(s) hex + payload hex.
    function base58check(versionHex, payloadHex) {
        const dataHex = versionHex + payloadHex;
        const chk = sha256hex(sha256hex(dataHex)).substring(0, 8);
        return b58encode(hexToBytes(dataHex + chk));
    }
    // Decode a base58check address -> { versionHex, payloadHex }. Throws on bad checksum.
    function base58checkDecode(addr) {
        const raw = b58decode(addr);
        if (raw.length < 5) throw new Error("Address too short.");
        const body = raw.slice(0, raw.length - 4);
        const chk = bytesToHex(raw.slice(raw.length - 4));
        const calc = sha256hex(sha256hex(bytesToHex(body))).substring(0, 8);
        if (chk !== calc) throw new Error("Bad address checksum.");
        return { versionHex: bytesToHex(body.slice(0, 1)), payloadHex: bytesToHex(body.slice(1)) };
    }

    // ---- Bech32 / Bech32m (BIP173 / BIP350) -----------------------------
    function bech32Polymod(values) {
        const GEN = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3];
        let chk = 1;
        for (const v of values) {
            const b = chk >> 25;
            chk = ((chk & 0x1ffffff) << 5) ^ v;
            for (let i = 0; i < 5; i++) if ((b >> i) & 1) chk ^= GEN[i];
        }
        return chk;
    }
    function hrpExpand(hrp) {
        const out = [];
        for (let i = 0; i < hrp.length; i++) out.push(hrp.charCodeAt(i) >> 5);
        out.push(0);
        for (let i = 0; i < hrp.length; i++) out.push(hrp.charCodeAt(i) & 31);
        return out;
    }
    function convertBits(data, from, to, pad) {
        let acc = 0, bits = 0; const out = []; const maxv = (1 << to) - 1;
        for (const value of data) {
            if (value < 0 || value >> from) throw new Error("Invalid data for bech32 conversion.");
            acc = (acc << from) | value; bits += from;
            while (bits >= to) { bits -= to; out.push((acc >> bits) & maxv); }
        }
        if (pad) { if (bits > 0) out.push((acc << (to - bits)) & maxv); }
        else if (bits >= from || ((acc << (to - bits)) & maxv)) throw new Error("Invalid padding in bech32.");
        return out;
    }
    function bech32Create(hrp, data, spec) {
        const values = hrpExpand(hrp).concat(data).concat([0, 0, 0, 0, 0, 0]);
        const constant = spec === 'bech32m' ? 0x2bc830a3 : 1;
        const mod = bech32Polymod(values) ^ constant;
        const out = [];
        for (let i = 0; i < 6; i++) out.push((mod >> (5 * (5 - i))) & 31);
        return out;
    }
    // Encode a segwit address. witver 0 -> bech32, 1+ -> bech32m.
    function segwitEncode(hrp, witver, programBytes) {
        const spec = witver === 0 ? 'bech32' : 'bech32m';
        const data = [witver].concat(convertBits(Array.from(programBytes), 8, 5, true));
        const combined = data.concat(bech32Create(hrp, data, spec));
        return hrp + '1' + combined.map(d => BECH32_CHARSET[d]).join('');
    }
    // Decode a segwit address -> { hrp, version, programHex }. Throws if invalid.
    function segwitDecode(addr) {
        const lower = addr.toLowerCase();
        if (addr !== lower && addr !== addr.toUpperCase()) throw new Error("Mixed-case bech32 address.");
        const pos = lower.lastIndexOf('1');
        if (pos < 1 || pos + 7 > lower.length) throw new Error("Invalid bech32 layout.");
        const hrp = lower.slice(0, pos);
        const dataChars = lower.slice(pos + 1);
        const data = [];
        for (const ch of dataChars) {
            const v = BECH32_CHARSET.indexOf(ch);
            if (v < 0) throw new Error("Invalid bech32 character.");
            data.push(v);
        }
        const witver = data[0];
        const spec = witver === 0 ? 'bech32' : 'bech32m';
        const check = bech32Polymod(hrpExpand(hrp).concat(data)) ^ (spec === 'bech32m' ? 0x2bc830a3 : 1);
        if (check !== 0) throw new Error("Bad bech32 checksum.");
        const program = convertBits(data.slice(1, data.length - 6), 5, 8, false);
        return { hrp, version: witver, programHex: bytesToHex(program) };
    }

    // ---- Bitcoin Cash CashAddr (bech32-like body, 40-bit BCH checksum) ----
    // Modern BCH addresses (bitcoincash:q… / p…) are NOT base58 — they use the
    // bech32 charset with a 40-bit polymod. Kept self-contained; reuses the
    // shared convertBits(). Verified against the CashAddr spec test vectors.
    const CASHADDR_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l";
    function cashPolymod(values) {
        let c = 1n;
        for (let i = 0; i < values.length; i++) {
            const c0 = c >> 35n;
            c = ((c & 0x07ffffffffn) << 5n) ^ BigInt(values[i]);
            if (c0 & 0x01n) c ^= 0x98f2bc8e61n;
            if (c0 & 0x02n) c ^= 0x79b76d99e2n;
            if (c0 & 0x04n) c ^= 0xf33e5fb3c4n;
            if (c0 & 0x08n) c ^= 0xae2eabe2a8n;
            if (c0 & 0x10n) c ^= 0x1e4f43e470n;
        }
        return c ^ 1n;
    }
    function cashPrefixExpand(prefix) {
        const out = [];
        for (let i = 0; i < prefix.length; i++) out.push(prefix.charCodeAt(i) & 0x1f);
        out.push(0);
        return out;
    }
    const _CASH_SIZE = { 20: 0, 24: 1, 28: 2, 32: 3, 40: 4, 48: 5, 56: 6, 64: 7 };
    // type: 0 = P2PKH, 1 = P2SH. hashHex is the 20-byte HASH160 (hex).
    function cashEncode(prefix, type, hashHex) {
        const hash = Array.from(hexToBytes(hashHex));
        const sizeBits = _CASH_SIZE[hash.length];
        if (sizeBits === undefined) throw new Error("Invalid CashAddr hash length.");
        const versionByte = (type << 3) | sizeBits;
        const payload5 = convertBits([versionByte].concat(hash), 8, 5, true);
        const mod = cashPolymod(cashPrefixExpand(prefix).concat(payload5).concat([0, 0, 0, 0, 0, 0, 0, 0]));
        const checksum5 = [];
        for (let i = 0; i < 8; i++) checksum5.push(Number((mod >> BigInt(5 * (7 - i))) & 0x1fn));
        return prefix + ':' + payload5.concat(checksum5).map(function (v) { return CASHADDR_CHARSET[v]; }).join('');
    }
    // -> { prefix, type, typeName, hashHex }. Accepts with or without the prefix.
    function cashDecode(addr) {
        let a = String(addr).toLowerCase().trim();
        let prefix, body;
        if (a.indexOf(':') >= 0) { const p = a.split(':'); prefix = p[0]; body = p[1]; }
        else { prefix = 'bitcoincash'; body = a; }
        if (!body) throw new Error("Empty CashAddr body.");
        const values = [];
        for (const ch of body) {
            const v = CASHADDR_CHARSET.indexOf(ch);
            if (v < 0) throw new Error("Invalid CashAddr character.");
            values.push(v);
        }
        if (cashPolymod(cashPrefixExpand(prefix).concat(values)) !== 0n) throw new Error("Bad CashAddr checksum.");
        const payloadBytes = convertBits(values.slice(0, values.length - 8), 5, 8, false);
        const versionByte = payloadBytes[0];
        const type = (versionByte >> 3) & 0x1f;
        return { prefix, type, typeName: type === 1 ? 'P2SH' : 'P2PKH', hashHex: bytesToHex(payloadBytes.slice(1)) };
    }

    // ---- Address derivation from a HASH160 ------------------------------
    // Returns { p2pkh, p2sh, bech32 } for a 20-byte pubkey-hash (hex).
    function addressesFromHash160(h160) {
        const redeem = "0014" + h160;                       // P2WPKH witness program
        return {
            p2pkh: base58check("00", h160),
            p2sh: base58check("05", hash160hex(redeem)),
            bech32: segwitEncode("bc", 0, hexToBytes(h160))
        };
    }
    // Same, parameterised by a network (version bytes + optional bech32 hrp) so
    // Litecoin / Dogecoin / Bitcoin Cash / Zcash-transparent reuse the exact same
    // base58check + segwit code as Bitcoin — only the version bytes differ.
    function addressesForNet(h160, net) {
        const out = { p2pkh: base58check(net.p2pkh, h160) };
        out.p2sh = base58check(net.p2sh, hash160hex("0014" + h160));
        if (net.hrp) out.bech32 = segwitEncode(net.hrp, 0, hexToBytes(h160));
        return out;
    }

    // ---- Base58 with an alternate alphabet (XRP uses its own dictionary) --
    const XRP_ALPHABET = "rpshnaf39wBUDNEGHJKLM4PQRST7VWXYZ2bcdeCg65jkm8oFqi1tuvAxyz";
    function b58encodeAlpha(bytes, alphabet) {
        let num = 0n;
        for (const b of bytes) num = num * 256n + BigInt(b);
        let str = "";
        while (num > 0n) { str = alphabet[Number(num % 58n)] + str; num /= 58n; }
        for (const b of bytes) { if (b === 0) str = alphabet[0] + str; else break; }
        return str || alphabet[0];
    }
    function b58decodeAlpha(str, alphabet) {
        let num = 0n;
        for (const ch of str) {
            const v = alphabet.indexOf(ch);
            if (v < 0) throw new Error("Invalid Base58 character.");
            num = num * 58n + BigInt(v);
        }
        let hex = num.toString(16); if (hex.length % 2) hex = '0' + hex;
        let bytes = Array.from(hexToBytes(hex));
        for (const ch of str) { if (ch === alphabet[0]) bytes.unshift(0); else break; }
        return new Uint8Array(bytes);
    }

    // ---- keccak-256 (EVM + Tron), via the site's Noble crypto loader ------
    // The site lazily exposes window.NobleHashes.sha3Module.keccak_256 (loaded by
    // window.CryptoLoader.load()). ensureNoble() triggers + waits for it so the
    // EVM / Tron / Sui tabs work even though this page sets needsCrypto:false.
    async function ensureNoble() {
        function ready() {
            return !!(window.NobleHashes && window.NobleHashes.sha3Module &&
                      window.NobleHashes.sha3Module.keccak_256);
        }
        if (ready()) return true;
        try { if (window.CryptoLoader && window.CryptoLoader.load) await window.CryptoLoader.load(); } catch (e) { /* fall through to poll */ }
        const t0 = Date.now();
        while (Date.now() - t0 < 9000) {
            if (ready()) return true;
            await new Promise(r => setTimeout(r, 40));
        }
        return ready();
    }
    function keccakBytes(bytes) { return bytesToHex(window.NobleHashes.sha3Module.keccak_256(bytes)); }
    function keccakHex(hex) { return keccakBytes(hexToBytes(hex)); }
    // EIP-55 mixed-case checksum for a 40-hex address (no 0x).
    function eip55(addrHex) {
        addrHex = addrHex.toLowerCase();
        const h = keccakBytes(new TextEncoder().encode(addrHex));
        let out = "";
        for (let i = 0; i < addrHex.length; i++) {
            const c = addrHex[i];
            out += /[0-9]/.test(c) ? c : (parseInt(h[i], 16) >= 8 ? c.toUpperCase() : c);
        }
        return "0x" + out;
    }
    // EVM address from a parsed secp256k1 key: keccak256(X‖Y) → last 20 bytes.
    function evmAddress(pk) { return eip55(keccakHex(pk.uncompressed.slice(2)).slice(-40)); }
    // Tron: same 20-byte hash, prefixed 0x41, base58check (double-SHA256, BTC alphabet).
    function tronAddress(pk) { return base58check("41", keccakHex(pk.uncompressed.slice(2)).slice(-40)); }
    // XRP: accountID = ripemd160(sha256(compressed)); base58check(v0x00) in the XRP alphabet.
    function xrpAddress(compressedHex) {
        const accountId = hash160hex(compressedHex);
        const dataHex = "00" + accountId;
        const chk = sha256hex(sha256hex(dataHex)).substring(0, 8);
        return b58encodeAlpha(hexToBytes(dataHex + chk), XRP_ALPHABET);
    }

    // ---- BLAKE2b-256 (Sui address hashing) ------------------------------
    // Compact BigInt implementation, verified against the RFC 7693 "abc" vector
    // (bddd813c…d52319). Only used for the tiny 33-byte Sui pre-image.
    const _B2B_IV = [
        0x6a09e667f3bcc908n, 0xbb67ae8584caa73bn, 0x3c6ef372fe94f82bn, 0xa54ff53a5f1d36f1n,
        0x510e527fade682d1n, 0x9b05688c2b3e6c1fn, 0x1f83d9abfb41bd6bn, 0x5be0cd19137e2179n];
    const _B2B_SIGMA = [
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
        [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4], [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
        [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13], [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
        [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11], [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
        [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5], [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3]];
    const _B2B_MASK = (1n << 64n) - 1n;
    function _b2bRotr(x, n) { return ((x >> n) | (x << (64n - n))) & _B2B_MASK; }
    function blake2b256(input) {
        let h = _B2B_IV.slice(); h[0] ^= 0x01010000n ^ 32n;
        let t = 0;
        const G = (v, a, b, c, d, x, y) => {
            v[a] = (v[a] + v[b] + x) & _B2B_MASK; v[d] = _b2bRotr(v[d] ^ v[a], 32n);
            v[c] = (v[c] + v[d]) & _B2B_MASK; v[b] = _b2bRotr(v[b] ^ v[c], 24n);
            v[a] = (v[a] + v[b] + y) & _B2B_MASK; v[d] = _b2bRotr(v[d] ^ v[a], 16n);
            v[c] = (v[c] + v[d]) & _B2B_MASK; v[b] = _b2bRotr(v[b] ^ v[c], 63n);
        };
        function compress(block, last) {
            const m = new Array(16);
            for (let i = 0; i < 16; i++) { let w = 0n; for (let j = 7; j >= 0; j--) w = (w << 8n) | BigInt(block[i * 8 + j]); m[i] = w; }
            const v = h.concat(_B2B_IV);
            v[12] = (v[12] ^ BigInt(t)) & _B2B_MASK;
            if (last) v[14] ^= _B2B_MASK;
            for (let r = 0; r < 12; r++) {
                const s = _B2B_SIGMA[r];
                G(v, 0, 4, 8, 12, m[s[0]], m[s[1]]); G(v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
                G(v, 2, 6, 10, 14, m[s[4]], m[s[5]]); G(v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
                G(v, 0, 5, 10, 15, m[s[8]], m[s[9]]); G(v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
                G(v, 2, 7, 8, 13, m[s[12]], m[s[13]]); G(v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
            }
            for (let i = 0; i < 8; i++) h[i] = (h[i] ^ v[i] ^ v[i + 8]) & _B2B_MASK;
        }
        const data = Array.from(input); let i = 0;
        if (data.length === 0) { compress(new Array(128).fill(0), true); }
        else {
            while (data.length - i > 128) { t += 128; compress(data.slice(i, i + 128), false); i += 128; }
            const rem = data.slice(i); t += rem.length;
            compress(rem.concat(new Array(128 - rem.length).fill(0)), true);
        }
        let out = "";
        for (let w = 0; w < 4; w++) { let val = h[w]; for (let b = 0; b < 8; b++) { out += Number(val & 0xffn).toString(16).padStart(2, '0'); val >>= 8n; } }
        return out;
    }
    // Sui ed25519 account address = 0x + blake2b256(0x00 ‖ 32-byte pubkey).
    function suiAddress(pubHex32) { return "0x" + blake2b256(hexToBytes("00" + pubHex32)); }

    // ---- Per-chain definitions (keyed by the tab's data-chain) -----------
    const CHAINS = {
        bitcoin:        { label: "Bitcoin",      kind: "btc", p2pkh: "00",   p2sh: "05",   hrp: "bc"  },
        litecoin:       { label: "Litecoin",     kind: "btc", p2pkh: "30",   p2sh: "32",   hrp: "ltc" },
        dogecoin:       { label: "Dogecoin",     kind: "btc", p2pkh: "1e",   p2sh: "16",   hrp: null  },
        "bitcoin-cash": { label: "Bitcoin Cash", kind: "btc", p2pkh: "00",   p2sh: "05",   hrp: null, cashaddr: "bitcoincash" },
        zcash:          { label: "Zcash",        kind: "btc", p2pkh: "1cb8", p2sh: "1cbd", hrp: null  },
        ethereum:       { label: "Ethereum",     kind: "evm" },
        bnb:            { label: "BNB Chain",     kind: "evm" },
        arbitrum:       { label: "Arbitrum",      kind: "evm" },
        optimism:       { label: "Optimism",      kind: "evm" },
        base:           { label: "Base",          kind: "evm" },
        polygon:        { label: "Polygon",       kind: "evm" },
        avalanche:      { label: "Avalanche",     kind: "evm" },
        zksync:         { label: "zkSync Era",     kind: "evm" },
        tron:           { label: "Tron",           kind: "tron" },
        xrp:            { label: "XRP",             kind: "xrp" },
        solana:         { label: "Solana",          kind: "sol" },
        sui:            { label: "Sui",              kind: "sui" },
        toncoin:        { label: "TON",               kind: "ton" }
    };
    function chainDef(c) { return CHAINS[c] || CHAINS.bitcoin; }
    function isSecpKind(k) { return k === "btc" || k === "evm" || k === "tron" || k === "xrp"; }

    // ---- Transaction parsing (for public-key recovery from an address) ---
    function readVarInt(buf, offset) {
        const prefix = buf[offset];
        if (prefix < 0xFD) return { val: prefix, size: 1 };
        if (prefix === 0xFD) return { val: buf[offset + 1] | (buf[offset + 2] << 8), size: 3 };
        if (prefix === 0xFE) return { val: buf[offset + 1] | (buf[offset + 2] << 8) | (buf[offset + 3] << 16) | (buf[offset + 4] << 24), size: 5 };
        return { val: buf[offset + 1], size: 9 };
    }
    function parseHexTransaction(txRaw) {
        const buf = hexToBytes(txRaw);
        let cursor = 4;                                      // skip version
        let isSegwit = false;
        if (buf[cursor] === 0x00 && buf[cursor + 1] === 0x01) { isSegwit = true; cursor += 2; }
        const inCount = readVarInt(buf, cursor); cursor += inCount.size;
        const inputs = [];
        for (let i = 0; i < inCount.val; i++) {
            cursor += 36;                                    // prevout hash + index
            const sLen = readVarInt(buf, cursor); cursor += sLen.size;
            const script_hex = bytesToHex(buf.slice(cursor, cursor + sLen.val)); cursor += sLen.val;
            cursor += 4;                                     // sequence
            inputs.push({ script_hex });
        }
        const outCount = readVarInt(buf, cursor); cursor += outCount.size;
        for (let i = 0; i < outCount.val; i++) {
            cursor += 8;                                     // value
            const sLen = readVarInt(buf, cursor); cursor += sLen.size + sLen.val;
        }
        if (isSegwit) {
            for (let i = 0; i < inCount.val; i++) {
                const wCount = readVarInt(buf, cursor); cursor += wCount.size;
                const witnesses = [];
                for (let j = 0; j < wCount.val; j++) {
                    const iLen = readVarInt(buf, cursor); cursor += iLen.size;
                    witnesses.push(bytesToHex(buf.slice(cursor, cursor + iLen.val)));
                    cursor += iLen.val;
                }
                inputs[i].witness = witnesses;
            }
        }
        return { inputs };
    }
    // Pull the first plausible compressed/uncompressed pubkey out of a scriptSig.
    function pubkeyFromScriptSig(scr) {
        const buf = hexToBytes(scr);
        for (let i = 0; i < buf.length; i++) {
            const len = buf[i];
            if ((len === 33 || len === 65) && i + 1 + len <= buf.length) {
                const cand = bytesToHex(buf.slice(i + 1, i + 1 + len));
                if (/^0[23][0-9a-f]{64}$/.test(cand) || /^04[0-9a-f]{128}$/.test(cand)) return cand;
            }
        }
        return "";
    }
    // Every public key exposed by the inputs of one transaction.
    function pubkeysFromTx(parsed) {
        const pubs = [];
        for (const inp of parsed.inputs) {
            if (inp.script_hex) { const p = pubkeyFromScriptSig(inp.script_hex); if (p) pubs.push(p); }
            if (inp.witness && inp.witness.length) {
                const w = inp.witness[inp.witness.length - 1];
                if (/^0[23][0-9a-f]{64}$/.test(w) || /^04[0-9a-f]{128}$/.test(w)) pubs.push(w);
            }
        }
        return pubs;
    }

    // ---- Network ---------------------------------------------------------
    async function getRawTx(txid) {
        const urls = [
            `https://blockstream.info/api/tx/${txid}/hex`,
            `https://blockchain.info/rawtx/${txid}?format=hex`
        ];
        for (const url of urls) {
            try {
                const resp = await fetch(url, { signal: AbortSignal.timeout(8000) });
                if (resp.ok) {
                    const raw = (await resp.text()).trim();
                    if (raw.length > 50 && !raw.includes("not found") && !raw.startsWith("<!DOCTYPE")) return raw;
                }
            } catch (e) { /* try next */ }
            await new Promise(r => setTimeout(r, 250));
        }
        throw new Error(`Could not fetch transaction ${txid.substring(0, 8)}…`);
    }
    // List an address's txids, newest first, up to `want`. Returns [] if none, null if every explorer failed.
    async function fetchAddressTxids(addr, want, onProgress) {
        let anyOk = false;
        try {
            let txids = [], lastSeen = '', guard = 0;
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
                if (onProgress) onProgress({ listed: txids.length, target: want });
                if (arr.length < 25) break;
                await new Promise(r => setTimeout(r, 120));
            }
            if (txids.length > 0) return txids.slice(0, want);
            if (anyOk) return [];
        } catch (e) { /* fall through */ }
        try {
            let txids = [], total = null, offset = 0; const PAGE = 50;
            while (txids.length < want) {
                const pageLimit = Math.min(PAGE, want - txids.length);
                const url = `https://blockchain.info/rawaddr/${addr}?limit=${pageLimit}&offset=${offset}&cors=true`;
                const resp = await fetch(url, { signal: AbortSignal.timeout(15000) });
                if (!resp.ok) break;
                anyOk = true;
                const data = await resp.json();
                if (!data || !Array.isArray(data.txs) || data.txs.length === 0) break;
                if (total === null) total = data.n_tx || 0;
                for (const tx of data.txs) txids.push(tx.hash);
                offset += data.txs.length;
                if (onProgress) onProgress({ listed: txids.length, target: Math.min(want, total || want) });
                if (total && offset >= total) break;
                if (data.txs.length < pageLimit) break;
                await new Promise(r => setTimeout(r, 150));
            }
            if (txids.length > 0) return txids.slice(0, want);
            if (anyOk) return [];
        } catch (e) { /* both failed */ }
        return anyOk ? [] : null;
    }

    // Recover the public key behind an address by scanning its spending txs.
    // The matching pubkey is the one whose hash160 maps to this exact address.
    async function recoverPubkeyForAddress(addr, targetH160, want, onProgress) {
        const txids = await fetchAddressTxids(addr, want, onProgress);
        if (txids === null) throw new Error("Couldn't reach a block explorer (it may be rate-limiting). Try again shortly.");
        if (txids.length === 0) return null;
        const BATCH = 4;
        let scanned = 0;
        for (let b = 0; b < txids.length; b += BATCH) {
            const slice = txids.slice(b, b + BATCH);
            const found = await Promise.all(slice.map(async (h) => {
                try {
                    const parsed = parseHexTransaction(await getRawTx(h));
                    for (const pub of pubkeysFromTx(parsed)) {
                        if (hash160hex(pub) === targetH160) return pub;
                    }
                } catch (e) { /* skip */ }
                return null;
            }));
            const hit = found.find(Boolean);
            if (hit) return hit;
            scanned += slice.length;
            if (onProgress) onProgress({ scanned, target: txids.length });
            await new Promise(r => setTimeout(r, 120));
        }
        return null;                                          // address never spent -> pubkey not revealed
    }

    // =====================================================================
    // Multi-chain public-key recovery from an address.
    // Every recoverer returns a public-key hex (secp256k1: 04/02/03…; ed25519:
    // 64-hex) that has been VERIFIED to re-derive the queried address, or null
    // when the address has never revealed its key on-chain. It NEVER returns an
    // unverified/guessed key. All data comes from keyless, CORS-enabled public
    // endpoints — the same ones the site's address-analysis tool already uses.
    // =====================================================================

    // ethers UMD (window.ethers) reconstructs EVM signing hashes across tx types
    // without hand-rolled RLP. Loaded lazily by window.CryptoLoader, like Noble.
    async function ensureEthers() {
        function ready() { return !!(window.ethers && window.ethers.Transaction && window.ethers.SigningKey); }
        if (ready()) return true;
        try { if (window.CryptoLoader && window.CryptoLoader.load) await window.CryptoLoader.load(); } catch (e) { /* poll */ }
        const t0 = Date.now();
        while (Date.now() - t0 < 9000) { if (ready()) return true; await new Promise(r => setTimeout(r, 40)); }
        return ready();
    }
    function nobleSecp() {
        const m = window.NobleCurves && window.NobleCurves.secp256k1Module;
        return m && m.secp256k1;
    }

    // ---- EVM (Ethereum + every EVM chain) — ECDSA ecrecover from a signed tx --
    // Per chain: a keyless tx LIST source (Blockscout v2 or Routescan) + a set of
    // public JSON-RPC hosts that serve the full signed transaction.
    const EVM_NET = {
        ethereum:  { list: ["eth.blockscout.com"],       rpc: ["https://ethereum-rpc.publicnode.com", "https://eth.llamarpc.com"] },
        arbitrum:  { list: ["arbitrum.blockscout.com"],  rpc: ["https://arbitrum-one-rpc.publicnode.com"] },
        optimism:  { list: ["explorer.optimism.io"],     rpc: ["https://optimism-rpc.publicnode.com", "https://mainnet.optimism.io"] },
        base:      { list: ["base.blockscout.com"],      rpc: ["https://base-rpc.publicnode.com"] },
        polygon:   { list: ["polygon.blockscout.com"],   rpc: ["https://polygon-bor-rpc.publicnode.com", "https://polygon.drpc.org"] },
        zksync:    { list: ["zksync.blockscout.com"],    rpc: ["https://mainnet.era.zksync.io"] },
        avalanche: { routescan: 43114,                   rpc: ["https://avalanche-c-chain-rpc.publicnode.com"] },
        bnb:       { routescan: 56,                      rpc: ["https://bsc-rpc.publicnode.com"] }
    };
    // List an address's OUTGOING tx hashes (from === addr) via Blockscout v2.
    // Returns [] if the address has none, null if the explorer was unreachable.
    async function blockscoutListFrom(host, addr, want, onProgress) {
        const al = addr.toLowerCase();
        let out = [], params = null, guard = 0, anyOk = false;
        while (out.length < want && guard < 20) {
            guard++;
            let url = "https://" + host + "/api/v2/addresses/" + encodeURIComponent(addr) + "/transactions";
            if (params) url += "?" + new URLSearchParams(params).toString();
            let resp;
            try { resp = await fetch(url, { headers: { "Accept": "application/json" }, signal: AbortSignal.timeout(15000) }); }
            catch (e) { break; }
            if (!resp.ok) break;
            anyOk = true;
            const d = await resp.json();
            const items = (d && Array.isArray(d.items)) ? d.items : [];
            for (const t of items) {
                if (t && t.from && t.from.hash && t.from.hash.toLowerCase() === al && t.hash) out.push(t.hash);
            }
            if (onProgress) onProgress({ listed: out.length, target: want });
            if (!d.next_page_params || items.length === 0) break;
            params = d.next_page_params;
            await new Promise(r => setTimeout(r, 150));
        }
        if (out.length) return out.slice(0, want);
        return anyOk ? [] : null;
    }
    // List outgoing tx hashes via Routescan's Etherscan-compatible API (Avalanche/BNB).
    async function routescanListFrom(chainId, addr, want) {
        const url = "https://api.routescan.io/v2/network/mainnet/evm/" + chainId +
            "/etherscan/api?module=account&action=txlist&address=" + encodeURIComponent(addr) +
            "&sort=desc&page=1&offset=" + want;
        let resp;
        try { resp = await fetch(url, { signal: AbortSignal.timeout(15000) }); } catch (e) { return null; }
        if (!resp.ok) return null;
        const d = await resp.json();
        if (d && d.status === "0" && d.message && /not supported|invalid/i.test(d.message)) return null;
        const list = (d && Array.isArray(d.result)) ? d.result : [];
        const al = addr.toLowerCase();
        return list.filter(t => t.from && t.from.toLowerCase() === al && t.hash).map(t => t.hash);
    }
    // First non-null JSON-RPC result across a chain's RPC hosts.
    async function evmRpc(rpcs, method, params) {
        for (const rpc of rpcs) {
            try {
                const resp = await fetch(rpc, {
                    method: "POST", headers: { "Content-Type": "application/json" },
                    body: JSON.stringify({ jsonrpc: "2.0", id: 1, method: method, params: params }),
                    signal: AbortSignal.timeout(12000)
                });
                if (!resp.ok) continue;
                const d = await resp.json();
                if (d && d.result !== undefined && d.result !== null) return d.result;
            } catch (e) { /* next host */ }
        }
        return null;
    }
    // Rebuild an ethers Transaction from an eth_getTransactionByHash object when
    // the node has no eth_getRawTransactionByHash. ethers recomputes .from.
    function evmTxFromObject(o) {
        const E = window.ethers;
        const ty = parseInt(o.type || "0x0", 16);
        const t = { type: ty, chainId: o.chainId, nonce: parseInt(o.nonce, 16), to: o.to, value: o.value, data: o.input, gasLimit: o.gas };
        const sig = { r: o.r, s: o.s };
        if (o.yParity !== undefined && o.yParity !== null) sig.yParity = parseInt(o.yParity, 16);
        else if (o.v !== undefined) sig.v = parseInt(o.v, 16);
        t.signature = sig;
        if (ty >= 2) { t.maxFeePerGas = o.maxFeePerGas; t.maxPriorityFeePerGas = o.maxPriorityFeePerGas; t.accessList = o.accessList || []; }
        else if (ty === 1) { t.gasPrice = o.gasPrice; t.accessList = o.accessList || []; }
        else { t.gasPrice = o.gasPrice; }
        return E.Transaction.from(t);
    }
    // recoverPublicKey from a parsed+signed ethers Transaction → uncompressed hex (no 0x).
    function pubFromEthersTx(tx) {
        const unc = window.ethers.SigningKey.recoverPublicKey(tx.unsignedHash, tx.signature); // 0x04…
        return unc.slice(2).toLowerCase();
    }
    async function evmRecoverOne(rpcs, hash, addrLower) {
        const E = window.ethers;
        const raw = await evmRpc(rpcs, "eth_getRawTransactionByHash", [hash]);
        if (raw && typeof raw === "string" && raw.length > 10) {
            try { const tx = E.Transaction.from(raw); if (tx.from && tx.from.toLowerCase() === addrLower) return pubFromEthersTx(tx); } catch (e) { /* try object */ }
        }
        const o = await evmRpc(rpcs, "eth_getTransactionByHash", [hash]);
        if (o) { try { const tx = evmTxFromObject(o); if (tx.from && tx.from.toLowerCase() === addrLower) return pubFromEthersTx(tx); } catch (e) { /* skip */ } }
        return null;
    }
    // addr must be the 0x… address. Returns uncompressed pubkey hex or null.
    async function recoverEvmPubkey(chain, addr, want, onProgress) {
        if (!(await ensureEthers()))
            throw new Error("Could not load the ethers library needed to reconstruct EVM signatures. Check your connection and try again.");
        const cfg = EVM_NET[chain];
        if (!cfg) throw new Error("Unsupported EVM chain.");
        let hashes = null;
        if (cfg.list) { for (const host of cfg.list) { hashes = await blockscoutListFrom(host, addr, want, onProgress); if (hashes) break; } }
        if ((!hashes || hashes.length === 0) && cfg.routescan != null) {
            const rs = await routescanListFrom(cfg.routescan, addr, want);
            if (rs !== null) hashes = rs;
        }
        if (hashes === null)
            throw new Error("Couldn't reach a keyless transaction source for " + chainDef(chain).label + " (it may be rate-limiting, or none is available for this chain). Try again shortly.");
        if (hashes.length === 0) return null;
        const al = addr.toLowerCase();
        let scanned = 0;
        for (const h of hashes) {
            const pub = await evmRecoverOne(cfg.rpc, h, al);
            scanned++;
            if (onProgress) onProgress({ scanned, target: hashes.length });
            if (pub) return pub;
            await new Promise(r => setTimeout(r, 60));
        }
        return null;
    }

    // ---- Tron — ECDSA ecrecover; Tron signs sha256(raw_data_hex) -------------
    async function tronListOwner(addr, want, onProgress) {
        // The key is only revealed by OUTGOING txs (ownerAddress === addr). An
        // active account can have many incoming txs between each send, so page
        // through more rows than `want` (up to 200) to make sure we surface the
        // outgoing ones — a single one is enough to recover the key.
        const seen = {}, out = [];
        let start = 0;
        const pageSize = 50;
        const maxScan = Math.min(Math.max(want * 5, 50), 200);
        let anyOk = false;
        while (out.length < want && start < maxScan) {
            const url = "https://apilist.tronscanapi.com/api/transaction?address=" + encodeURIComponent(addr) + "&limit=" + pageSize + "&start=" + start;
            let resp;
            try { resp = await fetch(url, { signal: AbortSignal.timeout(15000) }); } catch (e) { break; }
            if (!resp.ok) break;
            anyOk = true;
            const d = await resp.json();
            const list = (d && Array.isArray(d.data)) ? d.data : [];
            for (const t of list) {
                if (t.ownerAddress === addr && t.hash && !seen[t.hash]) { seen[t.hash] = 1; out.push(t.hash); }
            }
            if (onProgress) onProgress({ listed: out.length, target: want });
            if (list.length < pageSize) break;   // no more history
            start += pageSize;
            await new Promise(r => setTimeout(r, 150));
        }
        if (out.length) return out.slice(0, want);
        return anyOk ? [] : null;
    }
    async function tronRawTx(txid) {
        let resp;
        try {
            resp = await fetch("https://api.trongrid.io/wallet/gettransactionbyid", {
                method: "POST", headers: { "Content-Type": "application/json" },
                body: JSON.stringify({ value: txid }), signal: AbortSignal.timeout(12000)
            });
        } catch (e) { return null; }
        if (!resp.ok) return null;
        const d = await resp.json();
        if (!d || !d.raw_data_hex || !Array.isArray(d.signature) || !d.signature.length) return null;
        return { raw: d.raw_data_hex, sigs: d.signature };
    }
    // addr must be a T… base58 address. Returns uncompressed pubkey hex or null.
    async function recoverTronPubkey(addr, want, onProgress) {
        if (!(await ensureNoble())) throw new Error("Could not load the crypto library needed for Tron. Check your connection and try again.");
        const secp = nobleSecp();
        if (!secp) throw new Error("The secp256k1 library needed for Tron recovery is unavailable.");
        const dec = base58checkDecode(addr);
        if (dec.versionHex !== "41") throw new Error("Not a Tron address (version 0x" + dec.versionHex + ").");
        const targetH160 = dec.payloadHex.toLowerCase();
        const hashes = await tronListOwner(addr, want, onProgress);
        if (hashes === null) throw new Error("Couldn't reach Tronscan (it may be rate-limiting). Try again shortly.");
        if (hashes.length === 0) return null;
        let scanned = 0;
        for (const h of hashes) {
            const tx = await tronRawTx(h);
            scanned++;
            if (onProgress) onProgress({ scanned, target: hashes.length });
            if (!tx || !tx.sigs.length) continue;
            const digest = hexToBytes(sha256hex(tx.raw));
            // A tx may carry several signatures (multisig / permissioned accounts).
            // Try EVERY signature with both recovery bits; the key that hashes to
            // THIS address is the one we return — others simply won't match, so a
            // wrong key is never shown.
            for (const sh of tx.sigs) {
                if (!sh || sh.length < 128) continue;
                const r = sh.slice(0, 64), s = sh.slice(64, 128);
                for (let rec = 0; rec < 2; rec++) {
                    try {
                        const sig = new secp.Signature(BigInt("0x" + r), BigInt("0x" + s)).addRecoveryBit(rec);
                        const unc = sig.recoverPublicKey(digest).toHex(false);   // 04 + X + Y
                        if (keccakHex(unc.slice(2)).slice(-40).toLowerCase() === targetH160) return unc;
                    } catch (e) { /* wrong recovery bit */ }
                }
            }
            await new Promise(r => setTimeout(r, 60));
        }
        return null;
    }

    // ---- Bitcoin-family (Litecoin / Dogecoin / Bitcoin Cash) -----------------
    // Same scriptSig/witness parse as Bitcoin — only the tx source differs.
    function esploraList(base) {
        return async function (addr, want, onProgress) {
            let anyOk = false, txids = [], lastSeen = "", guard = 0;
            try {
                while (txids.length < want && guard < 200) {
                    guard++;
                    const url = lastSeen ? base + "/address/" + addr + "/txs/chain/" + lastSeen : base + "/address/" + addr + "/txs/chain";
                    const resp = await fetch(url, { signal: AbortSignal.timeout(15000) });
                    if (!resp.ok) break;
                    anyOk = true;
                    const arr = await resp.json();
                    if (!Array.isArray(arr) || !arr.length) break;
                    for (const t of arr) txids.push(t.txid);
                    lastSeen = arr[arr.length - 1].txid;
                    if (onProgress) onProgress({ listed: txids.length, target: want });
                    if (arr.length < 25) break;
                    await new Promise(r => setTimeout(r, 120));
                }
            } catch (e) { /* fall through */ }
            if (txids.length) return txids.slice(0, want);
            return anyOk ? [] : null;
        };
    }
    function esploraRaw(base) {
        return async function (txid) {
            const resp = await fetch(base + "/tx/" + txid + "/hex", { signal: AbortSignal.timeout(10000) });
            if (!resp.ok) return null;
            const t = (await resp.text()).trim();
            return /^[0-9a-fA-F]{40,}$/.test(t) ? t : null;
        };
    }
    function blockcypherList(coin) {
        return async function (addr, want, onProgress) {
            try {
                const url = "https://api.blockcypher.com/v1/" + coin + "/main/addrs/" + encodeURIComponent(addr) + "?limit=" + Math.min(want, 50);
                const resp = await fetch(url, { signal: AbortSignal.timeout(15000) });
                if (!resp.ok) return null;
                const d = await resp.json();
                const refs = (d && Array.isArray(d.txrefs)) ? d.txrefs : [];
                const seen = {}, out = [];
                for (const x of refs) { if (x.tx_hash && !seen[x.tx_hash]) { seen[x.tx_hash] = 1; out.push(x.tx_hash); } }
                if (onProgress) onProgress({ listed: out.length, target: want });
                return out.slice(0, want);
            } catch (e) { return null; }
        };
    }
    function blockcypherRaw(coin) {
        return async function (txid) {
            const resp = await fetch("https://api.blockcypher.com/v1/" + coin + "/main/txs/" + txid + "?includeHex=true", { signal: AbortSignal.timeout(10000) });
            if (!resp.ok) return null;
            const d = await resp.json();
            return (d && typeof d.hex === "string" && d.hex.length > 40) ? d.hex : null;
        };
    }
    function haskoinList(coin) {
        return async function (addr, want, onProgress) {
            try {
                const resp = await fetch("https://api.haskoin.com/" + coin + "/address/" + encodeURIComponent(addr) + "/transactions?limit=" + want, { signal: AbortSignal.timeout(15000) });
                if (!resp.ok) return null;
                const arr = await resp.json();
                if (!Array.isArray(arr)) return null;
                const out = arr.map(t => t.txid).filter(Boolean);
                if (onProgress) onProgress({ listed: out.length, target: want });
                return out.slice(0, want);
            } catch (e) { return null; }
        };
    }
    function haskoinRaw(coin) {
        return async function (txid) {
            const resp = await fetch("https://api.haskoin.com/" + coin + "/transaction/" + txid + "/raw", { signal: AbortSignal.timeout(10000) });
            if (!resp.ok) return null;
            const d = await resp.json();
            return (d && typeof d.result === "string" && d.result.length > 40) ? d.result : null;
        };
    }
    const BTC_SRC = {
        litecoin:       { list: esploraList("https://litecoinspace.org/api"), raw: esploraRaw("https://litecoinspace.org/api") },
        dogecoin:       { list: blockcypherList("doge"),                      raw: blockcypherRaw("doge") },
        "bitcoin-cash": { list: haskoinList("bch"),                          raw: haskoinRaw("bch") }
    };
    // scanAddr = the address to list (as the explorer expects it); targetH160 =
    // the 20-byte pubkey hash the recovered key must hash to. Returns pubkey hex or null.
    async function recoverBtcFamilyPubkey(chain, scanAddr, targetH160, want, onProgress) {
        const src = BTC_SRC[chain];
        if (!src) throw new Error("Public-key recovery isn't available for " + chainDef(chain).label + ".");
        const txids = await src.list(scanAddr, want, onProgress);
        if (txids === null) throw new Error("Couldn't reach a " + chainDef(chain).label + " explorer (it may be rate-limiting). Try again shortly.");
        if (txids.length === 0) return null;
        const BATCH = 4;
        let scanned = 0;
        for (let b = 0; b < txids.length; b += BATCH) {
            const slice = txids.slice(b, b + BATCH);
            const found = await Promise.all(slice.map(async (h) => {
                try {
                    const raw = await src.raw(h);
                    if (!raw) return null;
                    const parsed = parseHexTransaction(raw);
                    for (const pub of pubkeysFromTx(parsed)) if (hash160hex(pub) === targetH160) return pub;
                } catch (e) { /* skip */ }
                return null;
            }));
            const hit = found.find(Boolean);
            if (hit) return hit;
            scanned += slice.length;
            if (onProgress) onProgress({ scanned, target: txids.length });
            await new Promise(r => setTimeout(r, 120));
        }
        return null;
    }

    // ---- XRP — read SigningPubKey directly from a tx the account signed ------
    // Returns the SigningPubKey hex (secp256k1 02/03… or ed25519 ED…) or null.
    async function readXrpPubkey(addr, want, onProgress) {
        const url = "https://api.xrpscan.com/api/v1/account/" + encodeURIComponent(addr) + "/transactions?limit=" + want;
        let resp;
        try { resp = await fetch(url, { signal: AbortSignal.timeout(15000) }); }
        catch (e) { throw new Error("Couldn't reach xrpscan (it may be rate-limiting). Try again shortly."); }
        if (!resp.ok) { if (resp.status === 404) return null; throw new Error("Couldn't reach xrpscan (HTTP " + resp.status + ")."); }
        const d = await resp.json();
        const txs = (d && Array.isArray(d.transactions)) ? d.transactions : (Array.isArray(d) ? d : []);
        if (onProgress) onProgress({ listed: txs.length, target: want });
        for (const t of txs) {
            if (t && t.Account === addr && typeof t.SigningPubKey === "string" && t.SigningPubKey.length >= 64)
                return t.SigningPubKey.toLowerCase();
        }
        return null;
    }

    // ---- TON — the public key is published directly (no outgoing tx needed) --
    async function readTonPubkey(addr) {
        const url = "https://tonapi.io/v2/accounts/" + encodeURIComponent(addr) + "/publickey";
        let resp;
        try { resp = await fetch(url, { signal: AbortSignal.timeout(12000) }); }
        catch (e) { throw new Error("Couldn't reach tonapi (it may be rate-limiting). Try again shortly."); }
        if (!resp.ok) { if (resp.status === 404) return null; throw new Error("Couldn't reach tonapi (HTTP " + resp.status + ")."); }
        const d = await resp.json();
        return (d && typeof d.public_key === "string" && /^[0-9a-f]{64}$/i.test(d.public_key)) ? d.public_key.toLowerCase() : null;
    }

    // ---- Balance / Received / TX (same box as the R·S·Z tool) ------------
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
                const c = d.chain_stats || {}, m = d.mempool_stats || {};
                const funded = (c.funded_txo_sum || 0) + (m.funded_txo_sum || 0);
                const spent = (c.spent_txo_sum || 0) + (m.spent_txo_sum || 0);
                return { balance: funded - spent, received: funded, tx: (c.tx_count || 0) + (m.tx_count || 0) };
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
    // Rotating balance-check spinner — the same wheel the private-keys pages show
    // while an explorer request is in flight. Own class (.pkt-spin, not .fa-icon) so
    // the global icon-tint filters never recolour it; it is tinted + spun by tool.css.
    function spinner(size) {
        const n = size || 13;
        return '<img src="../assets/svgs/solid/spinner.svg" class="pkt-spin" width="' + n +
            '" height="' + n + '" alt="loading">';
    }
    function setStats(stats) {
        const b = document.getElementById('pkt-stat-balance');
        const r = document.getElementById('pkt-stat-received');
        const t = document.getElementById('pkt-stat-tx');
        // Turn the amount green when the address holds (Balance) or has ever held
        // (Received) coins — matching the private-keys balance colour (#22c55e).
        if (b) { b.textContent = stats ? formatBtc(stats.balance) : '0 BTC'; b.classList.toggle('has-balance', !!(stats && stats.balance > 0)); }
        if (r) { r.textContent = stats ? formatBtc(stats.received) : '0 BTC'; r.classList.toggle('has-balance', !!(stats && stats.received > 0)); }
        if (t) t.textContent = stats ? String(stats.tx) : '0';
    }
    // Show the spinner in the Balance / Received / TX boxes while their lookup runs.
    function statLoading() {
        ['pkt-stat-balance', 'pkt-stat-received', 'pkt-stat-tx'].forEach(function (id) {
            const el = document.getElementById(id);
            if (el) { el.innerHTML = spinner(16); el.classList.remove('has-balance'); }
        });
    }

    // Format a satoshi amount exactly like the private-keys balance pills: a sub-0.01 BTC
    // amount (< 1e6 sat) as a whole "N sat", otherwise BTC with trailing zeros trimmed.
    // The ₿ / ↓ pill icons imply the unit, so there is no "BTC" suffix here.
    function fmtAmt(sats) {
        const n = Number(sats || 0);
        if (n > 0 && n < 1e6) return n + ' sat';
        const s = (n / 1e8).toFixed(8).replace(/\.?0+$/, '');
        return s || '0';
    }
    // The per-address balance readout — identical markup to the private-keys pages:
    // a grey ₿ balance pill (orange when it holds coins), a blue ⇄ tx-count pill, and a
    // green ↓ received pill. Styled entirely by the site-wide style.min.css (.balance-info,
    // .bal/.tx/.recv + their .has-* funded states), which this page already loads.
    function balancePills(s) {
        const bal = Number(s.balance || 0), recv = Number(s.received || 0), tx = Number(s.tx || 0);
        return '<span class="balance-info">' +
            '<span class="bal' + (bal > 0 ? ' has-balance' : '') + '">' +
            '<img src="../assets/svgs/solid/bitcoin-sign.svg" class="fa-icon bal-icon" width="12" height="12" alt="">' +
            escapeHtml(fmtAmt(bal)) + '</span>' +
            '<span class="tx' + (tx > 0 ? ' has-tx' : '') + '">' +
            '<img src="../assets/svgs/solid/arrow-right-arrow-left.svg" class="fa-icon" width="10" height="10" alt="">' +
            tx + '</span>' +
            '<span class="recv' + (recv > 0 ? ' has-recv' : '') + '">' +
            '<img src="../assets/svgs/solid/arrow-down.svg" class="fa-icon" width="10" height="10" alt="">' +
            escapeHtml(fmtAmt(recv)) + '</span>' +
            '</span>';
    }

    // Fill the live balance slot under each derived address (Balance · Tx · Received).
    // Funds may sit on any address format, so every one is looked up independently.
    async function fillAddressBalances(root) {
        if (!root) return;
        const nodes = root.querySelectorAll('.pkt-addr-stats[data-bal]');
        await Promise.all(Array.prototype.map.call(nodes, async function (el) {
            const address = el.getAttribute('data-bal');
            try {
                const s = await fetchAddressStats(address);
                if (s) {
                    el.innerHTML = balancePills(s);
                    if (s.received > 0 || s.balance > 0) el.classList.add('pkt-has-funds');
                } else {
                    el.innerHTML = '<span class="balance-info"><span class="status">Balance unavailable</span></span>';
                    el.classList.add('pkt-bal-na');
                }
            } catch (e) {
                el.innerHTML = '<span class="balance-info"><span class="status">Balance unavailable</span></span>';
                el.classList.add('pkt-bal-na');
            }
        }));
    }

    // ---- HTML helpers (mirror the R·S·Z tool look) -----------------------
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
    function line(label, val, addr) {
        return '<div class="rsz-line"><span class="rsz-tag pkt-tag">' + escapeHtml(label) + '</span>' +
            '<code class="rsz-val ' + (addr ? 'rsz-addr-val' : '') + '">' + escapeHtml(val || '—') + '</code>' +
            copyBtn(val) + '</div>';
    }
    // Address line plus a slot that fillAddressBalances() populates with its live stats.
    function addrRow(label, address) {
        return line(label, address, true) +
            '<div class="pkt-addr-stats" data-bal="' + escapeHtml(address) + '">' +
            spinner(12) + ' Checking balance…</div>';
    }
    function fallbackCopy(text, done) {
        try {
            const ta = document.createElement('textarea');
            ta.value = text; ta.style.position = 'fixed'; ta.style.opacity = '0';
            document.body.appendChild(ta); ta.select(); document.execCommand('copy');
            document.body.removeChild(ta); done();
        } catch (e) { /* ignore */ }
    }
    document.addEventListener('click', function (ev) {
        const btn = ev.target && ev.target.closest ? ev.target.closest('.rsz-copy[data-copy]') : null;
        if (!btn) return;
        const val = btn.getAttribute('data-copy');
        const done = () => { btn.classList.add('copied'); setTimeout(() => btn.classList.remove('copied'), 1200); };
        if (navigator.clipboard && navigator.clipboard.writeText) {
            navigator.clipboard.writeText(val).then(done).catch(() => fallbackCopy(val, done));
        } else fallbackCopy(val, done);
    });

    function getOutputHeader() {
        return '<div class="result-header">CRYPTOGRAPHYTUBE<span class="tool-tag">Public Key Toolkit</span></div>' +
            '<div class="download-tools"><button class="btn-small btn-txt" title="Export as TXT" onclick="exportOne(\'pkt_out\',\'txt\')">' +
            '<img src="../assets/svgs/solid/download.svg" width="12" height="12" alt=""> SAVE TXT</button></div>';
    }

    // ---- Rendering -------------------------------------------------------
    // Full breakdown for a known public key (direct input or recovered).
    function renderPubkey(pk, note) {
        const h160c = hash160hex(pk.compressed);
        const h160u = hash160hex(pk.uncompressed);
        const a = addressesFromHash160(h160c);              // segwit uses the compressed hash
        let html = '';
        if (note) html += '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">' + escapeHtml(note) + '</span></div>';

        html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> Coordinates &amp; Public Key</div></div>';
        html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
        html += line('X (dec)', pk.x.toString(10));
        html += line('Y (dec)', pk.y.toString(10));
        html += line('X (hex)', to64(pk.x));
        html += line('Y (hex)', to64(pk.y));
        html += line('Compressed', pk.compressed);
        html += line('Uncompressed', pk.uncompressed);
        html += '</div></div>';

        html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/hashtag.svg" width="13" height="13" alt=""> HASH160 &amp; Addresses</div></div>';
        html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
        html += line('HASH160', h160c);
        html += addrRow('P2PKH (1…)', a.p2pkh);
        html += addrRow('P2SH-P2WPKH (3…)', a.p2sh);
        html += addrRow('Native SegWit (bc1…)', a.bech32);
        html += addrRow('P2PKH uncompressed', base58check('00', h160u));
        html += '</div></div>';
        return html;
    }

    // ---- Multi-chain rendering ------------------------------------------
    // The secp256k1 coordinate block is identical for every secp256k1 chain
    // (Bitcoin, EVM, Tron, XRP, Litecoin, …) — only the address encoding differs.
    function coordsBlock(pk) {
        let html = '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> Coordinates &amp; Public Key</div></div>';
        html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
        html += line('X (dec)', pk.x.toString(10));
        html += line('Y (dec)', pk.y.toString(10));
        html += line('X (hex)', to64(pk.x));
        html += line('Y (hex)', to64(pk.y));
        html += line('Compressed', pk.compressed);
        html += line('Uncompressed', pk.uncompressed);
        html += '</div></div>';
        return html;
    }
    // An address line; Bitcoin also gets the live balance slot (the balance API is
    // BTC-only, so other chains show the address without a — misleading — BTC balance).
    function addrLineForChain(chain, label, address) {
        return chain === 'bitcoin' ? addrRow(label, address) : line(label, address, true);
    }
    // Coordinates + this chain's address(es) for a known secp256k1 public key.
    // EVM/Tron need keccak, so the caller must have awaited ensureNoble() first.
    function renderSecpChain(chain, pk, note) {
        const net = chainDef(chain);
        let html = '';
        if (note) html += '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">' + escapeHtml(note) + '</span></div>';
        html += coordsBlock(pk);
        html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/wallet.svg" width="13" height="13" alt=""> ' + escapeHtml(net.label) + ' Address</div></div>';
        html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
        if (net.kind === 'btc') {
            const h160c = hash160hex(pk.compressed);
            const h160u = hash160hex(pk.uncompressed);
            const a = addressesForNet(h160c, net);
            html += line('HASH160', h160c);
            if (net.cashaddr) {
                html += addrLineForChain(chain, 'CashAddr (P2PKH)', cashEncode(net.cashaddr, 0, h160c));
                html += addrLineForChain(chain, 'Legacy P2PKH', a.p2pkh);
            } else {
                html += addrLineForChain(chain, 'P2PKH', a.p2pkh);
            }
            html += addrLineForChain(chain, 'P2SH-P2WPKH', a.p2sh);
            if (a.bech32) html += addrLineForChain(chain, 'Native SegWit', a.bech32);
            html += addrLineForChain(chain, 'P2PKH (uncompressed key)', base58check(net.p2pkh, h160u));
        } else if (net.kind === 'evm') {
            html += line(net.label + ' address', evmAddress(pk), true);
            html += '<div class="rsz-status">Ethereum &amp; every EVM chain (BNB, Arbitrum, Optimism, Base, Polygon, Avalanche, zkSync) share this same address.</div>';
        } else if (net.kind === 'tron') {
            html += line('Tron address (T…)', tronAddress(pk), true);
        } else if (net.kind === 'xrp') {
            html += line('XRP address (r…)', xrpAddress(pk.compressed), true);
        }
        html += '</div></div>';
        return html;
    }
    // ed25519 chains (Solana / Sui / TON) — a 32-byte ed25519 public key, NOT the
    // secp256k1 key Bitcoin uses. Accepts a 64-hex ed25519 key (or, for Solana, its
    // base58 address) and renders the chain address. Returns HTML or throws.
    function renderEd25519(chain, raw) {
        const net = chainDef(chain);
        const hx = raw.replace(/^0x/i, '').toLowerCase();
        let pubHex = null, note = '';

        if (chain === 'solana') {
            if (/^[0-9a-f]{64}$/.test(hx)) { pubHex = hx; note = '32-byte ed25519 public key'; }
            else {
                // A Solana address IS the base58 of the 32-byte ed25519 public key.
                try {
                    const dec = b58decode(raw.trim());
                    if (dec.length === 32) { pubHex = bytesToHex(dec); note = 'Decoded from a Solana address'; }
                } catch (e) { /* not base58 */ }
            }
            if (!pubHex) throw new Error('For Solana, paste a 32-byte (64-hex) ed25519 public key or a Solana address.');
            const address = b58encode(hexToBytes(pubHex));
            let html = '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">' + escapeHtml(note) + '</span></div>';
            html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> Solana (ed25519)</div></div>';
            html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
            html += line('Public key (hex)', pubHex);
            html += line('Address (base58)', address, true);
            html += '</div></div>';
            return html;
        }
        if (chain === 'sui') {
            if (/^[0-9a-f]{64}$/.test(hx)) {
                const address = suiAddress(hx);
                let html = '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">32-byte ed25519 public key</span></div>';
                html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> Sui (ed25519)</div></div>';
                html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
                html += line('Public key (hex)', hx);
                html += line('Address (0x)', address, true);
                html += '<div class="rsz-status">Sui address = blake2b256(0x00 ‖ ed25519 public key). A Sui address is a hash and cannot be reversed back to a public key.</div>';
                html += '</div></div>';
                return html;
            }
            throw new Error('For Sui, paste a 32-byte (64-hex) ed25519 public key.');
        }
        // TON — ed25519 key, but the on-chain address is derived from a chosen
        // wallet contract (v3R2 / v4R2 / …), so a bare public key has no single
        // canonical address. Show the key itself (honest — no fabricated address).
        if (chain === 'toncoin') {
            if (!/^[0-9a-f]{64}$/.test(hx)) throw new Error('For TON, paste a 32-byte (64-hex) ed25519 public key.');
            let html = '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">32-byte ed25519 public key</span></div>';
            html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> TON (ed25519)</div></div>';
            html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
            html += line('Public key (hex)', hx);
            html += '<div class="rsz-status">A TON wallet address is derived from a specific wallet contract (v3R2, v4R2, …) plus the workchain, so a bare public key maps to several possible addresses rather than one. The public key above is what every TON wallet for this key shares.</div>';
            html += '</div></div>';
            return html;
        }
        throw new Error('Unsupported chain.');
    }

    // ---- Recovery result helpers ----------------------------------------
    // Honest "nothing to recover" note — the address simply never revealed a key.
    function emptyRecovery(reason) {
        return '<div class="rsz-status rsz-empty">No public key found — ' + escapeHtml(reason) + '.</div>';
    }
    // XRP's SigningPubKey is read directly from a signed tx. It is secp256k1
    // (33-byte, 02/03…) for most accounts, or ed25519 (33-byte, ED-prefixed).
    // secp256k1 → full coordinate + address breakdown; ed25519 → key + address only.
    function renderXrpRecovered(addr, spkHex) {
        const hx = spkHex.toLowerCase();
        if (/^ed[0-9a-f]{64}$/.test(hx)) {
            const pub32 = hx.slice(2);
            let html = '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">Public key recovered from an on-chain signature (ed25519)</span></div>';
            html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> XRP (ed25519)</div></div>';
            html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
            html += line('SigningPubKey', hx);
            html += line('ed25519 public key', pub32);
            html += line('Address (r…)', addr, true);
            html += '<div class="rsz-status">This account signs with an ed25519 key (the ED prefix), not the secp256k1 key Bitcoin uses, so it has no X/Y curve coordinates.</div>';
            html += '</div></div>';
            return html;
        }
        if (/^0[23][0-9a-f]{64}$/.test(hx)) return renderSecpChain('xrp', parsePubkey(hx), 'Public key recovered from an on-chain signature');
        // Unexpected format — show it verbatim rather than guess.
        let html = '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">Public key recovered from an on-chain signature</span></div>';
        html += '<div class="rsz-row rsz-full"><div class="rsz-col">' + line('SigningPubKey', hx) + line('Address (r…)', addr, true) + '</div></div>';
        return html;
    }

    // TON publishes the ed25519 key for an account directly (readTonPubkey),
    // so it is recoverable even without an outgoing transaction.
    function renderTonRecovered(addr, pubHex) {
        const hx = (pubHex || '').toLowerCase();
        let html = '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">Public key recovered from TON (ed25519)</span></div>';
        html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/key.svg" width="13" height="13" alt=""> TON (ed25519)</div></div>';
        html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
        html += line('Address', addr, true);
        html += line('ed25519 public key', hx);
        html += '<div class="rsz-status">This is the ed25519 public key TON publishes for the account. A TON wallet address is derived from a specific wallet contract (v3R2, v4R2, …) plus the workchain, so the same key can back more than one address.</div>';
        html += '</div></div>';
        return html;
    }

    // ---- Address decoding ------------------------------------------------
    // -> { type, h160, program, addr }. h160 set for P2PKH / P2SH / P2WPKH.
    function decodeAddress(addr) {
        if (/^(bc1|tb1)/i.test(addr)) {
            const d = segwitDecode(addr);
            const type = d.programHex.length === 40 ? 'P2WPKH (native SegWit)'
                : d.programHex.length === 64 ? 'P2WSH / P2TR (native SegWit)'
                : 'SegWit v' + d.version;
            return { type, h160: d.programHex.length === 40 ? d.programHex : '', program: d.programHex, addr };
        }
        const d = base58checkDecode(addr);
        if (d.versionHex === '00') return { type: 'P2PKH (legacy)', h160: d.payloadHex, program: '', addr };
        if (d.versionHex === '05') return { type: 'P2SH', h160: '', program: d.payloadHex, addr };
        return { type: 'Base58 (version 0x' + d.versionHex + ')', h160: d.payloadHex, program: '', addr };
    }

    // ---- Main entry ------------------------------------------------------
    // Shared progress renderer for every recovery scan — same wording/spinner the
    // Bitcoin path uses ("Listing transactions…" then "Scanning transactions… n/N").
    function recoverProgress(out, header, html) {
        return function (p) {
            out.innerHTML = header + html + '<div class="rsz-status">' + spinner(14) + ' ' +
                (p.scanned != null
                    ? 'Scanning transactions… ' + p.scanned + ' / ' + p.target
                    : 'Listing transactions… ' + p.listed + (p.target ? ' / ' + p.target : '')) +
                '</div>';
        };
    }
    async function analyze() {
        const inputEl = document.getElementById('pkt_input');
        const out = document.getElementById('pkt_out');
        if (!inputEl || !out) return;
        const raw = inputEl.value.trim();
        if (!raw) return;

        const chain = (window.PKT_CHAIN || 'bitcoin');
        const net = chainDef(chain);
        const header = getOutputHeader();
        const status = (msg) => { out.innerHTML = header + '<div class="rsz-status">' + spinner(14) + ' ' + escapeHtml(msg) + '</div>'; };
        const scan = document.getElementById('pkt-scan');
        const limitEl = document.getElementById('pkt-tx-limit');
        let want = limitEl ? parseInt(limitEl.value, 10) : 20;
        if (!want || want < 1) want = 20;

        try {
            const hex = raw.replace(/^0x/i, '').toLowerCase();
            const isPubHex = /^0[23][0-9a-f]{64}$/.test(hex) || /^04[0-9a-f]{128}$/.test(hex);

            // ===== ed25519 chains (Solana / Sui / TON) — a different key system =====
            if (net.kind === 'sol' || net.kind === 'sui' || net.kind === 'ton') {
                setStats(null);
                if (isPubHex) {
                    // A secp256k1 key on an ed25519 chain: show its coords, but be clear it
                    // does not map to an address here.
                    out.innerHTML = header + renderSecpChain('bitcoin', parsePubkey(hex),
                        net.label + ' uses ed25519 keys — the secp256k1 key below has no ' + net.label +
                        ' address. Paste a 32-byte (64-hex) ed25519 public key' +
                        (chain === 'solana' ? ' or a Solana address.' : '.'));
                    return;
                }
                // A 64-hex ed25519 public key pasted directly — derive the address(es).
                if (/^[0-9a-f]{64}$/.test(hex)) { out.innerHTML = header + renderEd25519(chain, raw); return; }

                // Otherwise it's an address. Solana's address IS its ed25519 key, so
                // renderEd25519 decodes it locally (no network). Sui and TON need a
                // lookup — recover the real key when recovery is enabled.
                if (chain === 'solana') { out.innerHTML = header + renderEd25519(chain, raw); return; }

                if (chain === 'toncoin') {
                    if (scan && scan.checked) {
                        status('Fetching the public key from TON…');
                        let pub = null;
                        try { pub = await readTonPubkey(raw.trim()); }
                        catch (e) { out.innerHTML = header + '<div class="rsz-error">' + escapeHtml(e.message) + '</div>'; return; }
                        if (pub) { out.innerHTML = header + renderTonRecovered(raw.trim(), pub); return; }
                        out.innerHTML = header + '<div class="rsz-summary"><span class="rsz-chip">TON address</span></div>' +
                            emptyRecovery('TON has no published public key for this account (it may be uninitialised, or not a wallet contract)');
                        return;
                    }
                    out.innerHTML = header + '<div class="rsz-summary"><span class="rsz-chip">TON address</span></div>' +
                        '<div class="rsz-status">Enable “Recover public key from an address” to fetch this account’s ed25519 public key from TON, or paste a 32-byte (64-hex) ed25519 public key.</div>';
                    return;
                }
                // Sui — the public JSON-RPC that exposed transaction signatures has been
                // retired, so there is no keyless, browser-reachable way to recover a Sui
                // key from an address. Be honest rather than fabricate one.
                out.innerHTML = header + '<div class="rsz-summary"><span class="rsz-chip">Sui address</span></div>' +
                    '<div class="rsz-status">A Sui address is blake2b256(flag ‖ public key) — a hash, not reversible by math. Recovering the key would need a signed Sui transaction, but no keyless, browser-reachable Sui transaction API is currently available, so it can’t be recovered here. Paste a 32-byte (64-hex) ed25519 public key to derive the address.</div>';
                return;
            }

            // ===== secp256k1 chains (Bitcoin family, EVM, Tron, XRP) =====
            // 1) Public key -> shared coordinates + THIS chain's address(es).
            if (isPubHex) {
                setStats(null);
                if (net.kind === 'evm' || net.kind === 'tron') {
                    status('Loading key math…');
                    if (!(await ensureNoble()))
                        throw new Error('Could not load the keccak library needed for ' + net.label + '. Check your connection and try again.');
                }
                if (chain === 'bitcoin') {
                    out.innerHTML = header + renderPubkey(parsePubkey(hex),
                        hex.length === 66 ? 'Compressed public key' : 'Uncompressed public key');
                    fillAddressBalances(out);
                } else {
                    out.innerHTML = header + renderSecpChain(chain, parsePubkey(hex),
                        hex.length === 66 ? 'Compressed public key' : 'Uncompressed public key');
                }
                return;
            }

            // 2) EVM address input (40 hex, with or without 0x): validate + EIP-55 checksum,
            //    and — when recovery is enabled — ecrecover the public key from a signed tx.
            if (net.kind === 'evm' && /^[0-9a-f]{40}$/.test(hex)) {
                setStats(null);
                status('Checksumming address…');
                if (!(await ensureNoble())) throw new Error('Could not load the keccak library needed for EVM checksums.');
                const addr0x = '0x' + hex;
                let html = '<div class="rsz-summary"><span class="rsz-chip">' + escapeHtml(net.label) + ' address</span></div>';
                html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/wallet.svg" width="13" height="13" alt=""> ' + escapeHtml(net.label) + ' Address</div></div>';
                html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
                html += line('Checksummed (EIP-55)', eip55(hex), true);
                html += line('Lowercase', addr0x, true);
                html += '</div></div>';

                if (scan && scan.checked) {
                    out.innerHTML = header + html +
                        '<div class="rsz-status">' + spinner(14) + ' Scanning transactions to recover the public key…</div>';
                    const onProgress = recoverProgress(out, header, html);
                    let pub = null;
                    try { pub = await recoverEvmPubkey(chain, addr0x, want, onProgress); }
                    catch (e) { out.innerHTML = header + html + '<div class="rsz-error">' + escapeHtml(e.message) + '</div>'; return; }
                    if (pub) {
                        html += renderSecpChain(chain, parsePubkey(pub), 'Public key recovered from an on-chain signature');
                    } else {
                        html += '<div class="rsz-status rsz-empty">No public key found — this address has not sent a recoverable transaction' +
                            (chain === 'zksync' ? ' (zkSync’s native transaction type can’t be reconstructed)' :
                             chain === 'bnb' ? ', and no keyless BNB Chain transaction source is available' : '') +
                            ', so it never revealed its key on-chain.</div>';
                    }
                } else {
                    html += '<div class="rsz-status">An EVM address is keccak256(public key) truncated to 20 bytes — a hash, not reversible by math. Enable “Recover public key from an address” to ecrecover the key from a transaction this address signed.</div>';
                }
                out.innerHTML = header + html;
                return;
            }

            // 3) HASH160 (RIPEMD160 of a public key). Bitcoin keeps the full flow:
            //    derive its addresses, look up the balance, and — when recovery is
            //    enabled — scan the P2PKH address's spends for the public key it
            //    revealed on-chain (a hash can't be reversed to a key by math alone).
            if (chain === 'bitcoin' && /^[0-9a-f]{40}$/.test(hex)) {
                const a = addressesFromHash160(hex);
                status('Fetching balance…');
                statLoading();
                try { setStats(await fetchAddressStats(a.p2pkh)); } catch (e) { setStats(null); }

                let html = '<div class="rsz-summary"><span class="rsz-chip">HASH160 input</span></div>';
                html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/hashtag.svg" width="13" height="13" alt=""> HASH160 &amp; Addresses</div></div>';
                html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
                html += line('HASH160', hex);
                html += addrRow('P2PKH (1…)', a.p2pkh);
                html += addrRow('P2SH-P2WPKH (3…)', a.p2sh);
                html += addrRow('Native SegWit (bc1…)', a.bech32);
                html += '</div></div>';

                if (scan && scan.checked) {
                    out.innerHTML = header + html +
                        '<div class="rsz-status">' + spinner(14) + ' Scanning transactions to recover the public key…</div>';
                    const onProgress = (p) => {
                        out.innerHTML = header + html + '<div class="rsz-status">' + spinner(14) + ' ' +
                            (p.scanned != null
                                ? 'Scanning transactions… ' + p.scanned + ' / ' + p.target
                                : 'Listing transactions… ' + p.listed + (p.target ? ' / ' + p.target : '')) +
                            '</div>';
                    };
                    let pub = null;
                    try { pub = await recoverPubkeyForAddress(a.p2pkh, hex, want, onProgress); }
                    catch (e) { out.innerHTML = header + html + '<div class="rsz-error">' + escapeHtml(e.message) + '</div>'; return; }
                    if (pub) {
                        html += renderPubkey(parsePubkey(pub), 'Public key recovered from an on-chain signature');
                    } else {
                        html += '<div class="rsz-status rsz-empty">No public key found — this HASH160’s address has not spent funds yet, so it never revealed its key on-chain.</div>';
                    }
                } else {
                    html += '<div class="rsz-status">Enable “Recover public key from an address” to scan this HASH160’s transactions for the key revealed on-chain.</div>';
                }
                out.innerHTML = header + html;
                fillAddressBalances(out);
                return;
            }

            // 3b) HASH160 on another Bitcoin-family chain (Litecoin / Doge / BCH / Zcash):
            //     derive that chain's addresses, then — when recovery is enabled and a
            //     keyless source exists — scan the P2PKH address's spends for the key.
            if (net.kind === 'btc' && /^[0-9a-f]{40}$/.test(hex)) {
                setStats(null);
                const a = addressesForNet(hex, net);
                let html = '<div class="rsz-summary"><span class="rsz-chip">HASH160 input</span></div>';
                html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/hashtag.svg" width="13" height="13" alt=""> HASH160 &amp; ' + escapeHtml(net.label) + ' Addresses</div></div>';
                html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
                html += line('HASH160', hex);
                if (net.cashaddr) html += line('CashAddr (P2PKH)', cashEncode(net.cashaddr, 0, hex), true);
                html += line(net.cashaddr ? 'Legacy P2PKH' : 'P2PKH', a.p2pkh, true);
                html += line('P2SH-P2WPKH', a.p2sh, true);
                if (a.bech32) html += line('Native SegWit', a.bech32, true);
                html += '</div></div>';

                const scanAddr = net.cashaddr ? cashEncode('bitcoincash', 0, hex) : a.p2pkh;
                if (scan && scan.checked && BTC_SRC[chain]) {
                    out.innerHTML = header + html + '<div class="rsz-status">' + spinner(14) + ' Scanning transactions to recover the public key…</div>';
                    let pub = null;
                    try { pub = await recoverBtcFamilyPubkey(chain, scanAddr, hex, want, recoverProgress(out, header, html)); }
                    catch (e) { out.innerHTML = header + html + '<div class="rsz-error">' + escapeHtml(e.message) + '</div>'; return; }
                    if (pub) html += renderSecpChain(chain, parsePubkey(pub), 'Public key recovered from an on-chain signature');
                    else html += '<div class="rsz-status rsz-empty">No public key found — this address has not spent funds yet, so it never revealed its key on-chain.</div>';
                } else if (scan && scan.checked) {
                    html += '<div class="rsz-status">No keyless, browser-reachable transaction source is available for ' + escapeHtml(net.label) + ', so its public key can’t be recovered here. Paste a public key to derive every ' + escapeHtml(net.label) + ' address.</div>';
                } else {
                    html += '<div class="rsz-status">Enable “Recover public key from an address” to scan this HASH160’s transactions for the key revealed on-chain.</div>';
                }
                out.innerHTML = header + html;
                return;
            }

            // 4) Address input — Bitcoin keeps the full decode + recovery flow.
            if (chain === 'bitcoin') {
                status('Decoding address…');
                let dec;
                try { dec = decodeAddress(raw); }
                catch (e) { throw new Error('Unrecognised input. Paste a public key (02/03/04…), a 40-hex HASH160, or a Bitcoin address. (' + e.message + ')'); }

                status('Fetching balance…');
                statLoading();
                try { setStats(await fetchAddressStats(raw)); } catch (e) { setStats(null); }

                let html = '<div class="rsz-summary"><span class="rsz-chip">' + escapeHtml(dec.type) + '</span></div>';
                html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/wallet.svg" width="13" height="13" alt=""> Address</div></div>';
                html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
                html += line('Address', dec.addr, true);
                if (dec.h160) html += line('HASH160', dec.h160);
                if (dec.program && !dec.h160) html += line('Witness / script', dec.program);
                html += '</div></div>';

                const canRecover = dec.h160 && dec.h160.length === 40;
                if (scan && scan.checked && canRecover) {
                    out.innerHTML = header + html +
                        '<div class="rsz-status">' + spinner(14) + ' Scanning transactions to recover the public key…</div>';
                    const onProgress = (p) => {
                        out.innerHTML = header + html + '<div class="rsz-status">' + spinner(14) + ' ' +
                            (p.scanned != null
                                ? 'Scanning transactions… ' + p.scanned + ' / ' + p.target
                                : 'Listing transactions… ' + p.listed + (p.target ? ' / ' + p.target : '')) +
                            '</div>';
                    };
                    let pub = null;
                    try { pub = await recoverPubkeyForAddress(raw, dec.h160, want, onProgress); }
                    catch (e) { out.innerHTML = header + html + '<div class="rsz-error">' + escapeHtml(e.message) + '</div>'; return; }
                    if (pub) {
                        html += renderPubkey(parsePubkey(pub), 'Public key recovered from an on-chain signature');
                    } else {
                        html += '<div class="rsz-status rsz-empty">No public key found — this address has not spent funds yet, so it never revealed its key on-chain.</div>';
                    }
                } else if (canRecover) {
                    html += '<div class="rsz-status">Enable “Recover public key from an address” to scan transactions for the key revealed on-chain.</div>';
                } else {
                    html += '<div class="rsz-status">Public-key recovery is available for P2PKH / P2WPKH addresses (which commit to a single key).</div>';
                }
                out.innerHTML = header + html;
                fillAddressBalances(out);
                return;
            }

            // 4b) Address input on another secp256k1 chain — decode + validate, then
            //     recover the public key from real on-chain data when enabled:
            //       • XRP   → read SigningPubKey from a tx the account signed
            //       • Tron  → ecrecover from a signed transaction (sha256 digest)
            //       • LTC / DOGE / BCH → parse the scriptSig/witness of a spend
            //       • Zcash → no keyless browser-reachable tx source (honest message)
            status('Decoding address…');
            let rows, recover = null;
            try {
                rows = [];
                if (net.kind === 'xrp') {
                    const rawb = b58decodeAlpha(raw, XRP_ALPHABET);
                    if (rawb.length < 5) throw new Error('Address too short.');
                    const body = rawb.slice(0, rawb.length - 4);
                    const chk = bytesToHex(rawb.slice(rawb.length - 4));
                    if (sha256hex(sha256hex(bytesToHex(body))).substring(0, 8) !== chk) throw new Error('Bad checksum.');
                    rows.push(['Address', raw]);
                    rows.push(['Account ID (hex)', bytesToHex(body.slice(1))]);
                    recover = { kind: 'xrp' };
                } else if (/^(bc1|ltc1|tb1)/i.test(raw)) {
                    const d = segwitDecode(raw);
                    rows.push(['Address', raw]);
                    rows.push(['Witness v' + d.version + ' program', d.programHex]);
                    if (chain === 'litecoin' && d.programHex.length === 40) recover = { kind: 'btc', scanAddr: raw, h160: d.programHex };
                } else if (chain === 'bitcoin-cash') {
                    // BCH: modern CashAddr (bitcoincash:q…/p…) or legacy base58 (1…/3…).
                    let type, h160;
                    try { const c = cashDecode(raw); type = c.type; h160 = c.hashHex; }
                    catch (e1) { const d = base58checkDecode(raw); type = d.versionHex === '05' ? 1 : 0; h160 = d.payloadHex; }
                    if (h160.length !== 40) throw new Error('Unexpected hash length.');
                    rows.push(['Address', raw]);
                    rows.push(['Type', type === 1 ? 'P2SH' : 'P2PKH']);
                    rows.push(['HASH160 (hex)', h160]);
                    rows.push(['CashAddr', cashEncode('bitcoincash', type, h160)]);
                    rows.push(['Legacy (base58)', base58check(type === 1 ? '05' : '00', h160)]);
                    if (type === 0) recover = { kind: 'btc', scanAddr: cashEncode('bitcoincash', 0, h160), h160: h160 };
                } else if (net.kind === 'tron') {
                    // Tron: base58check with version byte 0x41. The 20-byte payload is
                    // the SAME keccak-derived hash as this key's EVM (Ethereum) address,
                    // so from a T-address we can also show its equivalent 0x… address.
                    const d = base58checkDecode(raw);
                    if (d.versionHex !== '41') throw new Error('Not a Tron address (version 0x' + d.versionHex + ', expected 0x41).');
                    if (d.payloadHex.length !== 40) throw new Error('Unexpected Tron payload length.');
                    rows.push(['Address', raw]);
                    rows.push(['Version byte', '0x41']);
                    rows.push(['HASH160 (hex)', d.payloadHex]);
                    if (await ensureNoble()) rows.push(['Ethereum / EVM address', eip55(d.payloadHex)]);
                    recover = { kind: 'tron' };
                } else {
                    const d = base58checkDecode(raw);
                    rows.push(['Address', raw]);
                    rows.push(['Version byte', '0x' + d.versionHex]);
                    rows.push([d.payloadHex.length === 40 ? 'HASH160 (hex)' : 'Payload (hex)', d.payloadHex]);
                    // Litecoin / Dogecoin legacy P2PKH (version 0x30 / 0x1e) — recover by scanning.
                    if (BTC_SRC[chain] && d.payloadHex.length === 40 && d.versionHex === net.p2pkh)
                        recover = { kind: 'btc', scanAddr: raw, h160: d.payloadHex };
                }
            } catch (e) {
                throw new Error('Could not read this as a ' + net.label + ' address. Paste a public key (02/03/04…) or a valid ' + net.label + ' address. (' + e.message + ')');
            }
            setStats(null);
            let html = '<div class="rsz-summary"><span class="rsz-chip">' + escapeHtml(net.label) + ' address</span></div>';
            html += '<div class="rsz-thead rsz-full"><div><img src="../assets/svgs/solid/wallet.svg" width="13" height="13" alt=""> ' + escapeHtml(net.label) + ' Address</div></div>';
            html += '<div class="rsz-row rsz-full"><div class="rsz-col">';
            for (const [lbl, val] of rows) html += line(lbl, val, /address|hash160|cashaddr|legacy|account id|payload|program/i.test(lbl));
            html += '</div></div>';

            if (scan && scan.checked && recover) {
                out.innerHTML = header + html + '<div class="rsz-status">' + spinner(14) + ' Recovering the public key from on-chain data…</div>';
                const onProgress = recoverProgress(out, header, html);
                try {
                    if (recover.kind === 'xrp') {
                        const spk = await readXrpPubkey(raw, want, onProgress);
                        if (spk) html += renderXrpRecovered(raw, spk);
                        else html += emptyRecovery('this account has not submitted a signed transaction yet, so it never revealed its key on-chain');
                    } else if (recover.kind === 'tron') {
                        const pub = await recoverTronPubkey(raw, want, onProgress);
                        if (pub) html += renderSecpChain(chain, parsePubkey(pub), 'Public key recovered from an on-chain signature');
                        else html += emptyRecovery('this address has not sent a single-signature transaction, so it never revealed its key on-chain');
                    } else {   // btc-family
                        const pub = await recoverBtcFamilyPubkey(chain, recover.scanAddr, recover.h160, want, onProgress);
                        if (pub) html += renderSecpChain(chain, parsePubkey(pub), 'Public key recovered from an on-chain signature');
                        else html += emptyRecovery('this address has not spent funds yet, so it never revealed its key on-chain');
                    }
                } catch (e) { out.innerHTML = header + html + '<div class="rsz-error">' + escapeHtml(e.message) + '</div>'; return; }
            } else if (scan && scan.checked) {
                html += '<div class="rsz-status">Public-key recovery isn’t available for this address type on ' + escapeHtml(net.label) +
                    (chain === 'zcash' ? ' — no keyless, browser-reachable Zcash transaction source exists (and shielded z-addresses have no public key by design).' : ' (only single-key addresses commit to one recoverable key).') +
                    ' Paste a public key to derive every ' + escapeHtml(net.label) + ' address.</div>';
            } else {
                const note = net.kind === 'tron'
                    ? 'This 20-byte HASH160 is identical on Tron and every EVM chain (Ethereum, BNB, Polygon, …), so one private key controls them all. Enable “Recover public key from an address” to ecrecover the key from a transaction this address signed.'
                    : 'Enable “Recover public key from an address” to recover the key ' + escapeHtml(net.label) + ' revealed on-chain, or paste a public key to derive every ' + escapeHtml(net.label) + ' address.';
                html += '<div class="rsz-status">' + note + '</div>';
            }
            out.innerHTML = header + html;
        } catch (e) {
            out.innerHTML = header + '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Error: ' +
                escapeHtml(e.message) + '</div>';
        }
    }

    // ---- Export ----------------------------------------------------------
    function exportOne(id, type) {
        const el = document.getElementById(id);
        if (!el || el.innerText.trim().length < 5 || el.innerText.includes('Instructions:')) {
            alert('No results to export yet.'); return;
        }
        let text = 'CRYPTOGRAPHYTUBE REPORT\nTOOL: PUBLIC KEY TOOLKIT\nGENERATED: ' +
            new Date().toLocaleString() + '\n' + '-'.repeat(50) + '\n\n' + (el.innerText || el.textContent);
        if (type === 'txt') {
            const url = URL.createObjectURL(new Blob([text], { type: 'text/plain' }));
            const a = document.createElement('a');
            a.href = url; a.download = 'CryptographyTube_PublicKeyToolkit.txt';
            document.body.appendChild(a); a.click(); document.body.removeChild(a);
        }
    }

    // ---- Expose ----------------------------------------------------------
    window.PublicKeyToolkit = { analyze: analyze, setStats: setStats };
    window.exportOne = exportOne;
})();

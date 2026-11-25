/*
 * BIP32 non-hardened parent-key leak -> master private-key recovery.
 * Engine extracted from the CryptographyTube Tools collection.
 * Self-contained: depends only on CryptoJS (crypto-js) which is loaded
 * before this file. Exposes window.processTxid() and window.exportOne().
 *
 * This is a DIRECT-INPUT tool (no block-explorer fetch). Paste a parent xpub,
 * ONE non-hardened child private key and its index — it recovers the parent
 * master private key entirely offline and self-verified.
 *
 * Threat model — BIP32 unhardened derivation is reversible if a single child
 * private key ever leaks. The public parent chain code lives inside the xpub,
 * so anyone holding the xpub + one exposed child key can walk BACK up the tree:
 *
 *      I  = HMAC-SHA512( chainCode , serP(K_par) || ser32(i) )
 *      IL = I[0..32)
 *      k_child = (IL + k_par) mod n           (BIP32 CKDpriv, forward)
 *  =>  k_par   = (k_child - IL) mod n          (the leak, backward)
 *
 * The x-only public parent K_par is embedded in the xpub, so the recovered
 * k_par is ACCEPTED only when k_par*G == K_par — mathematically certain, not a
 * guess. From k_par we rebuild the whole parent node (xprv), so the ENTIRE
 * subtree of that xpub is compromised.
 *
 * HARDENED indices (i >= 2^31) are immune: CKDpriv-hardened hashes the parent
 * PRIVATE key, which the xpub does not contain — such inputs are refused.
 */
(function () {
    "use strict";

    const ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    const N = BigInt('0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141');
    const HARDENED = 0x80000000;   // 2^31: indices >= this are hardened (immune)

    // ---- secp256k1 math --------------------------------------------------
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
    function pubFromPriv(d) { return compressPoint(sMul(d)); }

    // ---- Hashing / address (CryptoJS) ------------------------------------
    function sha256hex(hex) { return CryptoJS.SHA256(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function ripe160hex(hex) { return CryptoJS.RIPEMD160(CryptoJS.enc.Hex.parse(hex)).toString(); }
    function dblsha256(hex) { return sha256hex(sha256hex(hex)); }
    function hmacSha512hex(dataHex, keyHex) {
        return CryptoJS.HmacSHA512(CryptoJS.enc.Hex.parse(dataHex), CryptoJS.enc.Hex.parse(keyHex)).toString();
    }
    function b58encode(hex) {
        let num = BigInt("0x" + hex);
        let str = "";
        while (num > 0n) { str = ALPHABET[Number(num % 58n)] + str; num /= 58n; }
        for (let i = 0; i < hex.length; i += 2) { if (hex.substring(i, i + 2) === "00") str = "1" + str; else break; }
        return str;
    }
    function b58decode(str) {
        let num = 0n;
        for (let i = 0; i < str.length; i++) {
            const idx = ALPHABET.indexOf(str[i]);
            if (idx < 0) throw new Error("invalid base58 character '" + str[i] + "'");
            num = num * 58n + BigInt(idx);
        }
        let hex = num === 0n ? "" : num.toString(16);
        if (hex.length % 2) hex = "0" + hex;
        let zeros = "";
        for (let i = 0; i < str.length && str[i] === "1"; i++) zeros += "00";
        return zeros + hex;
    }
    function b58checkDecode(str) {
        const full = b58decode(str);
        if (full.length < 10) throw new Error("string too short to be Base58Check");
        const payload = full.slice(0, -8);
        const checksum = full.slice(-8);
        if (dblsha256(payload).slice(0, 8) !== checksum) throw new Error("bad Base58Check checksum");
        return payload;
    }
    function b58check(hex) { return b58encode(hex + dblsha256(hex).slice(0, 8)); }

    function hash160ToAddress(hash160, version_byte) {
        const versioned = version_byte + hash160;
        return b58encode(versioned + dblsha256(versioned).slice(0, 8));
    }
    function pubToAddr_P2PKH(pub_hex) { return hash160ToAddress(ripe160hex(sha256hex(pub_hex)), "00"); }
    function privToWif(d) { const p = "80" + hx(d) + "01"; return b58encode(p + dblsha256(p).slice(0, 8)); }
    function ser32(n) { return (n >>> 0).toString(16).padStart(8, "0"); }

    // Extended-key version bytes we understand (all carry a compressed pubkey).
    const XPUB_VERSIONS = {
        "0488b21e": { net: "Bitcoin mainnet", label: "xpub", xprv: "0488ade4" },
        "049d7cb2": { net: "Bitcoin mainnet (P2WPKH-in-P2SH)", label: "ypub", xprv: "049d7878" },
        "04b24746": { net: "Bitcoin mainnet (P2WPKH)", label: "zpub", xprv: "04b2430c" },
        "043587cf": { net: "Bitcoin testnet", label: "tpub", xprv: "04358394" },
        "044a5262": { net: "Bitcoin testnet (P2WPKH-in-P2SH)", label: "upub", xprv: "044a4e28" },
        "045f1cf6": { net: "Bitcoin testnet (P2WPKH)", label: "vpub", xprv: "045f18bc" }
    };

    // ---- Input parsing ---------------------------------------------------
    function parseIndexToken(t) {
        t = String(t == null ? "" : t).trim().toLowerCase();
        if (!t) throw new Error("child index is required");
        // hardened notation: 5', 5h, 5H  -> flag hardened
        let hardened = false;
        if (/['h]$/.test(t)) { hardened = true; t = t.replace(/['h]$/, ""); }
        let i;
        if (/^0x[0-9a-f]+$/.test(t)) i = Number(BigInt(t));
        else if (/^[0-9]+$/.test(t)) i = Number(t);
        else throw new Error("index must be a non-negative integer (got \"" + t + "\")");
        if (!Number.isFinite(i) || i < 0) throw new Error("index must be a non-negative integer");
        if (hardened) i += HARDENED;   // e.g. 0' == 2^31
        return i;
    }
    function parseChildKey(t) {
        t = String(t == null ? "" : t).trim();
        if (!t) throw new Error("child private key is required");
        // strip an optional 0x prefix; accept WIF too
        if (/^(0x)?[0-9a-fA-F]{64}$/.test(t)) return BigInt("0x" + t.replace(/^0x/i, ""));
        if (/^[5KL9c][1-9A-HJ-NP-Za-km-z]{50,51}$/.test(t)) {   // WIF (mainnet/testnet)
            const dec = b58decode(t);
            const body = dec.slice(0, -8);            // drop checksum
            let hexKey = body.slice(2);               // drop version byte
            if (hexKey.length === 66 && hexKey.slice(-2) === "01") hexKey = hexKey.slice(0, 64); // compressed flag
            if (hexKey.length !== 64) throw new Error("unrecognised WIF payload length");
            return BigInt("0x" + hexKey);
        }
        throw new Error("child private key must be 64 hex chars (or a WIF)");
    }
    function normalizeXpub(t) {
        return String(t == null ? "" : t).replace(/\s+/g, "").trim();
    }

    // ---- Recovery core ---------------------------------------------------
    function recoverParent(xpubStr, childStr, indexStr) {
        const xpub = normalizeXpub(xpubStr);
        if (!xpub) throw new Error("parent xpub is required");

        const payload = b58checkDecode(xpub);
        if (payload.length !== 156) throw new Error("not an extended key (expected a 78-byte payload, got " + (payload.length / 2) + " bytes)");
        const version = payload.slice(0, 8).toLowerCase();
        const vinfo = XPUB_VERSIONS[version];
        const depth = payload.slice(8, 10);
        const parentFP = payload.slice(10, 18);
        const childNum = payload.slice(18, 26);
        const chainCode = payload.slice(26, 90);
        const keyData = payload.slice(90, 156).toLowerCase();

        if (keyData.slice(0, 2) === "00") {
            throw new Error("this is an extended PRIVATE key (xprv) — paste the PUBLIC xpub instead");
        }
        if (keyData.slice(0, 2) !== "02" && keyData.slice(0, 2) !== "03") {
            throw new Error("extended key does not contain a compressed public key");
        }
        const K_par = keyData;   // 33-byte compressed parent pubkey

        const i = parseIndexToken(indexStr);
        const hardened = i >= HARDENED;
        const kc = parseChildKey(childStr);
        if (kc <= 0n || kc >= N) throw new Error("child private key is out of range for secp256k1");

        // Base result carries the parsed context so the UI can explain refusals.
        const ctx = {
            version: version, versionInfo: vinfo, depth: depth, parentFP: parentFP,
            childNum: childNum, chainCode: chainCode, K_par: K_par,
            index: i, hardened: hardened, childPriv: hx(kc)
        };

        if (hardened) {
            // CKDpriv-hardened hashes the parent PRIVATE key (0x00||k_par), which the
            // xpub does not contain. The public parent-key leak cannot apply here.
            return Object.assign(ctx, { ok: false, refused: true });
        }

        // I = HMAC-SHA512(chainCode, serP(K_par) || ser32(i));  IL = I[:32]
        const I = hmacSha512hex(K_par + ser32(i), chainCode);
        const IL = BigInt("0x" + I.slice(0, 64));
        if (IL >= N) {
            // negligible probability; such a child index is invalid per BIP32
            return Object.assign(ctx, { ok: false, refused: false, ilInvalid: true });
        }

        // The leak:  k_par = (k_child - IL) mod n
        const k_par = mod(kc - IL, N);
        const derivedPub = compressPoint(sMul(k_par));
        const ok = derivedPub === K_par;

        if (!ok) return Object.assign(ctx, { ok: false, refused: false, IL: hx(IL), derivedPub: derivedPub });

        // Rebuild the whole parent node: WIF, P2PKH address, and — when we know the
        // version — the parent extended PRIVATE key (xprv), which owns the subtree.
        const pubFull = K_par;
        const wif = privToWif(k_par);
        const addr = pubToAddr_P2PKH(pubFull);
        let xprv = null;
        if (vinfo) {
            const xprvHex = (vinfo.xprv + depth + parentFP + childNum + chainCode + "00" + hx(k_par)).toLowerCase();
            xprv = b58check(xprvHex);
        }
        return Object.assign(ctx, {
            ok: true, refused: false, IL: hx(IL),
            parentPriv: hx(k_par), wif: wif, pub: pubFull, addr: addr, xprv: xprv
        });
    }

    // ---- Output header + export ------------------------------------------
    function getOutputHeader(elementId) {
        let header = `<div class="result-header">CRYPTOGRAPHYTUBE<span class="tool-tag">BIP32 Parent-Key Recovery</span></div>`;
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
        let rawText = el.innerText || el.textContent;
        let headerText = `CRYPTOGRAPHYTUBE REPORT\nTOOL: BIP32 PARENT-KEY RECOVERY\nGENERATED: ${new Date().toLocaleString()}\n--------------------------------------------------\n\n`;
        const fullContent = headerText + rawText;
        if (type === 'txt') {
            const blob = new Blob([fullContent], { type: 'text/plain' });
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url; a.download = `CryptographyTube_Report_${id}.txt`;
            document.body.appendChild(a); a.click(); document.body.removeChild(a);
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
    function rszLine(label, val, cls) {
        return '<div class="rsz-line"><span class="rsz-tag">' + label + '</span>' + monoCell(val, cls) + '</div>';
    }
    function fallbackCopy(text, done) {
        try {
            const ta = document.createElement('textarea');
            ta.value = text; ta.style.position = 'fixed'; ta.style.opacity = '0';
            document.body.appendChild(ta); ta.select();
            document.execCommand('copy'); document.body.removeChild(ta); done();
        } catch (e) { }
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

    // ---- Rendering -------------------------------------------------------
    function renderResults(res) {
        let html = '<div class="rsz-leak-box">';

        if (res.ok) {
            html += '<div class="rsz-summary"><span class="rsz-chip rsz-chip-danger">Parent master key recovered</span>' +
                '<span class="rsz-chip">non-hardened index ' + res.index + '</span>' +
                (res.versionInfo ? '<span class="rsz-chip">' + escapeHtml(res.versionInfo.label + ' · ' + res.versionInfo.net) + '</span>' : '') +
                '</div>';
            html += '<div class="rsz-leak-note"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> ' +
                '<span>One leaked non-hardened child key walked back up the tree. The recovered parent private key is ' +
                '<strong>verified</strong> — <code>k_par&middot;G</code> equals the public key embedded in the xpub — so the ' +
                '<strong>entire subtree</strong> under this xpub is compromised. This is certain, not a guess.</span></div>';
            html += '</div>';

            html += '<div class="rsz-vuln-box">';
            html += '<div class="rsz-vuln-title"><img src="../assets/svgs/solid/key.svg" width="15" height="15" alt=""> Recovered parent node</div>';
            html += '<div class="rsz-vuln-key"><span class="key-label">PARENT PRIV (hex)</span><code class="rsz-val private-key">' + escapeHtml(res.parentPriv) + '</code>' + copyBtn(res.parentPriv) + '</div>';
            html += '<div class="rsz-vuln-key"><span class="key-label">PARENT WIF</span><code class="rsz-val private-key">' + escapeHtml(res.wif) + '</code>' + copyBtn(res.wif) + '</div>';
            if (res.xprv) html += '<div class="rsz-vuln-key"><span class="key-label">PARENT XPRV</span><code class="rsz-val private-key">' + escapeHtml(res.xprv) + '</code>' + copyBtn(res.xprv) + '</div>';
            html += rszLine('PARENT PUB', res.pub);
            html += '<div class="rsz-line"><span class="rsz-tag">ADDRESS</span><code class="rsz-val rsz-addr-val">' + escapeHtml(res.addr) + '</code>' + copyBtn(res.addr) + '</div>';
            html += '</div>';
        } else if (res.refused) {
            html += '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">Hardened — immune</span>' +
                '<span class="rsz-chip">index ' + (res.index - HARDENED) + '&prime; (' + res.index + ')</span></div>';
            html += '<div class="rsz-leak-note"><span>Index <strong>' + (res.index - HARDENED) + '&prime;</strong> is <strong>hardened</strong> ' +
                '(&ge; 2<sup>31</sup>). BIP32 hardened derivation hashes the parent <em>private</em> key, which an xpub does not contain, so a ' +
                'leaked child key here reveals <strong>nothing</strong> about the parent. This is exactly why hardened derivation exists — the ' +
                'attack does not apply. Use a non-hardened index (0 &le; i &lt; 2<sup>31</sup>) to demonstrate the leak.</span></div>';
            html += '</div>';
        } else if (res.ilInvalid) {
            html += '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">Invalid child</span></div>';
            html += '<div class="rsz-leak-note"><span>The derived <code>IL</code> is &ge; n, which BIP32 defines as an invalid child index. ' +
                'This child does not exist for this parent; try the next index.</span></div>';
            html += '</div>';
        } else {
            html += '<div class="rsz-summary"><span class="rsz-chip rsz-chip-ok">No recovery</span></div>';
            html += '<div class="rsz-leak-note"><span>These inputs are <strong>not consistent</strong>: the key derived from ' +
                '<code>(k_child &minus; IL)</code> does not match the public key inside this xpub. Check that (1) the child private key ' +
                'really belongs to <strong>this</strong> xpub, and (2) the <strong>index</strong> is the exact non-hardened index used to ' +
                'derive it. A single wrong digit breaks the match.</span></div>';
            html += '</div>';
        }

        // Echo the parsed context so the user can audit the derivation.
        html += '<div class="rsz-vuln-box">';
        html += '<div class="rsz-vuln-title"><img src="../assets/svgs/solid/circle-info.svg" width="15" height="15" alt=""> Derivation inputs</div>';
        html += rszLine('VERSION', res.version + (res.versionInfo ? '  (' + res.versionInfo.label + ')' : '  (unknown)'));
        html += rszLine('PARENT PUB (from xpub)', res.K_par);
        html += rszLine('CHAIN CODE', res.chainCode);
        html += rszLine('CHILD PRIV', res.childPriv, 'private-key');
        html += rszLine('INDEX', String(res.hardened ? (res.index - HARDENED) + "' (hardened)" : res.index));
        if (res.IL) html += rszLine('IL = HMAC-SHA512[:32]', res.IL);
        if (res.derivedPub) html += rszLine('DERIVED PUB (mismatch)', res.derivedPub);
        html += '</div>';

        return html;
    }

    // ---- Main entry ------------------------------------------------------
    async function processTxid() {
        const xpubEl = document.getElementById("xpub_input");
        const childEl = document.getElementById("child_input");
        const indexEl = document.getElementById("index_input");
        const out = document.getElementById("out_txid");
        if (!xpubEl || !out) return;

        const header = getOutputHeader(out.id);
        const xpubVal = xpubEl.value.trim();
        const childVal = childEl ? childEl.value.trim() : "";
        const indexVal = indexEl ? indexEl.value.trim() : "";

        if (!xpubVal && !childVal) {
            out.innerHTML = header + '<div class="rsz-status">Enter a parent <code>xpub</code>, one non-hardened child private key, and its index.</div>';
            return;
        }

        out.innerHTML = header + '<div class="rsz-status"><img src="../assets/svgs/solid/spinner.svg" class="txr-spin" width="14" height="14" alt=""> Deriving&hellip;</div>';
        await new Promise(function (r) { setTimeout(r, 20); });

        try {
            const res = recoverParent(xpubVal, childVal, indexVal);
            out.innerHTML = header + renderResults(res);
        } catch (e) {
            out.innerHTML = header +
                '<div class="rsz-error"><img src="../assets/svgs/solid/triangle-exclamation.svg" width="14" height="14" alt=""> Error: ' +
                escapeHtml(e.message) + '</div>';
        }
    }

    window.processTxid = processTxid;
    window.exportOne = exportOne;
})();

/*!
 * balance-fix.js — direct, CORS-enabled balance checking for SUI / XRP / Zcash / Solana.
 *
 * Why this file exists
 * --------------------
 * Four chains in the wallet-search originally depended on infrastructure that
 * does not exist on the static site:
 *   • SUI  used https://fullnode.mainnet.sui.io — public JSON-RPC there is now
 *          DEPRECATED, so every call returned an error.
 *   • XRP  posted to the relative path /api/xrp   (a server proxy that was never
 *   • ZEC  posted to the relative path /api/zec    deployed → 404 on GitHub Pages
 *          and cPanel, which have no backend).
 *   • SOL  posted to SOLANA_API / SOLANA_ACTIVITY_API (CSRF-guarded server proxy,
 *          same story) → the balance column hung on its spinner forever.
 * The result was the "RPC Error / All RPCs failed" / endless "waiting" the user
 * reported for exactly these coins while the other chains worked.
 *
 * This patch replaces BalanceChecker.fetch{Sui,Xrp,Zcash,Solana}BalancesBatch with
 * implementations that talk to public, CORS-enabled endpoints straight from the
 * browser. The Map<address, value> return shapes are kept byte-for-byte identical
 * to the originals (verified against the deobfuscated source) so the results grid,
 * the found-wallet logic and every other consumer render unchanged.
 *
 *   SUI  -> suix_getBalance on public Sui JSON-RPC nodes (publicnode / suiscan / 1rpc)
 *   XRP  -> account_info on public XRPL clusters (reuses fetchXrpAddressWithRetry;
 *           actNotFound = unfunded = balance 0), with an xrpscan REST fallback
 *   ZEC  -> Blockchair per-address dashboards (free, CORS *), Tatum fallback;
 *           fanned out in parallel chunks so a full page resolves in seconds
 *   SOL  -> getMultipleAccounts on public Solana JSON-RPC (publicnode / mainnet-beta /
 *           1rpc / drpc), up to 100 pubkeys per request; lamports / 1e9 = SOL
 *
 * Loaded with `defer` immediately AFTER balance-checker.obf.js, so window.BalanceChecker
 * already exists; a short poll covers any unexpected ordering.
 */
(function () {
  'use strict';

  /* Convert a decimal string ("56.774133") to integer base units (drops/zatoshi). */
  function toBaseUnits(dec, decimals) {
    dec = String(dec == null ? '0' : dec).trim();
    var neg = dec.charAt(0) === '-';
    if (neg) dec = dec.slice(1);
    var parts = dec.split('.');
    var whole = parts[0] || '0';
    var frac = (parts[1] || '').replace(/[^0-9]/g, '');
    frac = (frac + '00000000000000000000').slice(0, decimals);
    var v = BigInt(whole || '0') * (10n ** BigInt(decimals)) + BigInt(frac || '0');
    return neg ? -v : v;
  }

  function patch(BC) {
    if (!BC || BC.__cgtBalanceFix) return;
    BC.__cgtBalanceFix = true;

    /* ============================================================= SUI === */
    var SUI_RPCS = [
      'https://sui-rpc.publicnode.com',
      'https://rpc-mainnet.suiscan.xyz',
      'https://1rpc.io/sui',
      'https://fullnode.mainnet.sui.io:443'
    ];
    // Keep the shared config pointed at a live node too — checkSuiAddressActive()
    // and any other reader of SUI_CONFIG.rpc use it.
    if (BC.SUI_CONFIG) BC.SUI_CONFIG.rpc = SUI_RPCS[0];

    BC.fetchSuiBalancesBatch = async function (addresses, opts) {
      var out = new Map();
      if (this.isBot) return out;
      if (!addresses || addresses.length === 0) return out;
      var self = this;

      for (var i = 0; i < addresses.length; i += 5) {
        var slice = addresses.slice(i, i + 5);
        await Promise.all(slice.map(async function (addr) {
          try {
            var result = null, lastErr = null;
            for (var e = 0; e < SUI_RPCS.length; e++) {
              try {
                var resp = await self.fetchWithTimeout(SUI_RPCS[e], {
                  method: 'POST',
                  headers: { 'Content-Type': 'application/json' },
                  body: JSON.stringify({ jsonrpc: '2.0', id: 1, method: 'suix_getBalance', params: [addr] })
                }, 12000);
                var j = await resp.json();
                if (j && j.result) { result = j.result; break; }
                lastErr = new Error((j && j.error && j.error.message) || 'No result');
              } catch (ex) { lastErr = ex; }
            }
            if (!result) throw (lastErr || new Error('All Sui RPCs failed'));

            var bal = BigInt(result.totalBalance || '0');
            var coinCount = result.coinObjectCount || 0;
            var active = bal > 0n || coinCount > 0;
            if (!active) { try { active = await self.checkSuiAddressActive(addr); } catch (e2) {} }
            var f = self.formatSuiBalance(bal);
            out.set(addr, { balance: bal, balanceStr: f.value, symbol: f.unit, txCount: coinCount, active: active });
          } catch (err) {
            out.set(addr, { balance: 0n, balanceStr: '0', symbol: 'SUI', txCount: 0, active: false, error: true, errorMessage: err && err.message });
          }
        }));
        if (i + 5 < addresses.length) await this.sleep(100);
      }
      return out;
    };

    /* ============================================================= XRP === */
    BC.fetchXrpBalancesBatch = async function (addresses, opts) {
      var out = new Map();
      if (this.isBot) return out;
      if (!addresses || addresses.length === 0) return out;

      for (var i = 0; i < addresses.length; i++) {
        var addr = addresses[i];
        var bal = null, activated = false, seq = 0, ok = false;

        // Primary: direct XRPL JSON-RPC (account_info) across the configured
        // clusters — this method already handles actNotFound = unfunded = 0.
        try {
          var r = await this.fetchXrpAddressWithRetry(addr, 2);
          if (r && r.balance !== undefined && r.balance !== null) {
            bal = BigInt(r.balance); activated = !!r.activated; seq = r.sequence || 0; ok = true;
          }
        } catch (e) {}

        // Fallback: xrpscan REST (CORS *, returns xrpBalance in decimal XRP).
        if (!ok) {
          try {
            var resp = await this.fetchWithTimeout('https://api.xrpscan.com/api/v1/account/' + addr, { method: 'GET' }, 12000);
            var j = await resp.json();
            if (j && j.error && j.error.error === 'actNotFound') {
              bal = 0n; activated = false; seq = 0; ok = true;               // unfunded → 0
            } else if (j && (j.xrpBalance != null || j.Balance != null)) {
              bal = (j.Balance != null) ? BigInt(j.Balance) : toBaseUnits(j.xrpBalance, 6);
              activated = true; seq = j.sequence || j.Sequence || 0; ok = true;
            }
          } catch (e2) {}
        }

        if (ok) {
          var f = this.formatXrpBalance(bal);
          out.set(addr, { balance: bal, balanceStr: f.value, symbol: f.unit, txCount: seq, active: activated || bal > 0n, activated: activated });
        } else {
          out.set(addr, { balance: 0n, balanceStr: '0', symbol: 'XRP', txCount: 0, active: false, activated: false, error: true, errorMessage: 'All XRP endpoints failed' });
        }
      }
      return out;
    };

    /* ============================================================= ZEC === */
    // Look up ONE Zcash address (Blockchair primary, Tatum fallback) and return
    // the value object in the exact shape the grid / found-wallet logic consumes.
    async function zcashOne(self, addr) {
      var val = null;

      // Primary: Blockchair single-address dashboard (free tier, CORS *).
      try {
        var resp = await self.fetchWithTimeout(
          'https://api.blockchair.com/zcash/dashboards/address/' + encodeURIComponent(addr) + '?limit=0',
          { method: 'GET' }, 12000);
        var j = await resp.json();
        var a = j && j.data && j.data[addr] && j.data[addr].address;
        if (a) {
          var bal = BigInt(a.balance || 0);
          var rec = BigInt(a.received || 0);
          var spent = BigInt(a.spent || 0);
          var f = self.formatZcashBalance(bal);
          val = {
            balance: bal, balanceStr: f.value,
            received: rec, receivedStr: self.formatZcashBalance(rec).value,
            spent: spent, symbol: f.unit,
            txCount: a.transaction_count || 0,
            active: bal > 0n || rec > 0n,
            firstSeen: a.first_seen_receiving || null,
            lastSeen: a.last_seen_receiving || null,
            firstSpent: a.first_seen_spending || null,
            lastSpent: a.last_seen_spending || null
          };
        }
      } catch (e) {}

      // Fallback: Tatum (works when the monthly credit window resets).
      if (!val) {
        try {
          var key = (typeof self.getNextTatumKey === 'function')
            ? self.getNextTatumKey()
            : (self.TATUM_KEYS && self.TATUM_KEYS[0]);
          if (key) {
            var tr = await self.fetchWithTimeout('https://api.tatum.io/v3/zcash/address/balance/' + encodeURIComponent(addr),
              { method: 'GET', headers: { 'x-api-key': key } }, 12000);
            if (tr.ok) {
              var tj = await tr.json();
              var inc = toBaseUnits(tj.incoming || '0', 8);
              var outg = toBaseUnits(tj.outgoing || '0', 8);
              var bal2 = inc - outg; if (bal2 < 0n) bal2 = 0n;
              var f2 = self.formatZcashBalance(bal2);
              val = {
                balance: bal2, balanceStr: f2.value,
                received: inc, receivedStr: self.formatZcashBalance(inc).value,
                spent: outg, symbol: f2.unit, txCount: 0,
                active: bal2 > 0n || inc > 0n,
                firstSeen: null, lastSeen: null, firstSpent: null, lastSpent: null
              };
            }
          }
        } catch (e3) {}
      }

      if (!val) {
        val = { balance: 0n, balanceStr: '0', received: 0n, receivedStr: '0', spent: 0n, symbol: 'ZEC', txCount: 0, active: false, error: true, errorMessage: 'All Zcash APIs failed' };
      }
      return val;
    }

    // Blockchair also exposes a MULTI-address dashboard
    // (/zcash/dashboards/addresses/a,b,c,…) that returns EVERY address in a
    // single request — data.addresses[addr] carries balance/received/spent/
    // transaction_count directly. One call per ~50 addresses instead of one call
    // per address is what makes a full page resolve in ~1s. Returns only the
    // addresses the call actually answered; the caller falls back per-address for
    // any it missed, so this is never worse than the old per-address path.
    async function zcashBatchBlockchair(self, slice) {
      var got = new Map();
      try {
        var url = 'https://api.blockchair.com/zcash/dashboards/addresses/'
          + slice.map(encodeURIComponent).join(',') + '?limit=0';
        var resp = await self.fetchWithTimeout(url, { method: 'GET' }, 15000);
        var j = await resp.json();
        var addrs = j && j.data && j.data.addresses;
        if (addrs) {
          slice.forEach(function (addr) {
            var a = addrs[addr];
            if (!a) return;
            var bal = BigInt(a.balance || 0);
            var rec = BigInt(a.received || 0);
            var spent = BigInt(a.spent || 0);
            var f = self.formatZcashBalance(bal);
            got.set(addr, {
              balance: bal, balanceStr: f.value,
              received: rec, receivedStr: self.formatZcashBalance(rec).value,
              spent: spent, symbol: f.unit,
              txCount: a.transaction_count || 0,
              active: bal > 0n || rec > 0n,
              firstSeen: a.first_seen_receiving || null,
              lastSeen: a.last_seen_receiving || null,
              firstSpent: a.first_seen_spending || null,
              lastSpent: a.last_seen_spending || null
            });
          });
        }
      } catch (e) {}
      return got;
    }

    // Batch the whole page through the multi-address dashboard (BATCH addresses
    // per request); any address the batch didn't return is resolved in parallel
    // by zcashOne (single Blockchair dashboard, then Tatum). Same return shape as
    // before — seconds → sub-second for a typical page.
    BC.fetchZcashBalancesBatch = async function (addresses, opts) {
      opts = opts || {};
      var out = new Map();
      if (this.isBot) return out;
      if (!addresses || addresses.length === 0) return out;
      var self = this;
      var onProgress = opts.onProgress || null;
      var done = 0;
      var BATCH = 50;

      for (var i = 0; i < addresses.length; i += BATCH) {
        var slice = addresses.slice(i, i + BATCH);
        var got = await zcashBatchBlockchair(self, slice);

        var missing = slice.filter(function (a) { return !got.has(a); });
        if (missing.length) {
          await Promise.all(missing.map(async function (addr) {
            got.set(addr, await zcashOne(self, addr));
          }));
        }

        slice.forEach(function (addr) {
          var val = got.get(addr);
          out.set(addr, val);
          if (onProgress) { try { onProgress(addr, val, done, addresses.length); } catch (e4) {} }
          done++;
        });

        if (i + BATCH < addresses.length) await this.sleep(120);   // small gap between batches (free tier)
      }
      return out;
    };

    /* ============================================================= SOL === */
    // The engine's original fetchSolanaBalancesBatch POSTs to a server proxy
    // (SOLANA_API / SOLANA_ACTIVITY_API, CSRF-guarded) that does not exist on the
    // static site, so the Solana balance column hung on its spinner forever
    // ("waiting"). Replace it with public, CORS-enabled Solana JSON-RPC
    // getMultipleAccounts — up to 100 pubkeys per call, so one request per page.
    // lamports / 1e9 = SOL. Return shape matches the SUI/ZEC patches exactly.
    var SOL_RPCS = [
      'https://solana-rpc.publicnode.com',
      'https://api.mainnet-beta.solana.com',
      'https://1rpc.io/sol',
      'https://solana.drpc.org'
    ];
    var SOL_DECIMALS = 9;
    function formatSol(lamports) {
      var v = (typeof lamports === 'bigint') ? lamports : BigInt(lamports || 0);
      var base = 10n ** BigInt(SOL_DECIMALS);
      var whole = (v / base).toString();
      var frac = (v % base).toString().padStart(SOL_DECIMALS, '0').replace(/0+$/, '');
      return frac ? (whole + '.' + frac) : whole;
    }

    BC.fetchSolanaBalancesBatch = async function (addresses, opts) {
      opts = opts || {};
      var out = new Map();
      if (this.isBot) return out;
      if (!addresses || addresses.length === 0) return out;
      var self = this;
      var onProgress = opts.onProgress || null;
      var done = 0;

      for (var i = 0; i < addresses.length; i += 100) {
        var slice = addresses.slice(i, i + 100);
        var vals = null, lastErr = null;

        for (var r = 0; r < SOL_RPCS.length && !vals; r++) {
          try {
            var resp = await self.fetchWithTimeout(SOL_RPCS[r], {
              method: 'POST',
              headers: { 'Content-Type': 'application/json' },
              body: JSON.stringify({
                jsonrpc: '2.0', id: 1, method: 'getMultipleAccounts',
                params: [slice, { encoding: 'base64', dataSlice: { offset: 0, length: 0 } }]
              })
            }, 12000);
            var j = await resp.json();
            if (j && j.result && j.result.value) { vals = j.result.value; break; }
            lastErr = new Error((j && j.error && j.error.message) || 'No result');
          } catch (ex) { lastErr = ex; }
        }

        slice.forEach(function (addr, k) {
          var val;
          if (vals) {
            var acct = vals[k];
            var lamports = acct ? BigInt(acct.lamports || 0) : 0n;
            val = { balance: lamports, balanceStr: formatSol(lamports), symbol: 'SOL', txCount: 0, active: lamports > 0n };
          } else {
            val = { balance: 0n, balanceStr: '0', symbol: 'SOL', txCount: 0, active: false, error: true, errorMessage: (lastErr && lastErr.message) || 'All Solana RPCs failed' };
          }
          out.set(addr, val);
          if (onProgress) { try { onProgress(addr, val, done, addresses.length); } catch (e5) {} }
          done++;
        });

        if (i + 100 < addresses.length) await this.sleep(100);
      }
      return out;
    };

    /* ============================================================= BCH === */
    // The engine's original fetchBitcoinCashBalancesBatch lowercased every
    // address before sending it to haskoin:
    //     addresses.map(a => a.toLowerCase().replace('bitcoincash:',''))
    // That is fine for a cashaddr (already lowercase) but CORRUPTS a legacy
    // base58 address ("1BgGZ9tcN4rm..." -> "1bggz9tcn4rm..."), which is
    // case-sensitive. haskoin then answers the whole batch with
    //     {"error":"user-error","message":"Unable to parse param addresses"}
    // so EVERY balance on the page fell back to 0 — a FALSE zero, i.e. fake
    // data. It only "worked" on a cashaddr page. Legacy BCH addresses appear
    // whenever the page is reached with ?type=legacy (e.g. the Bitcoin->Bitcoin
    // Cash tab used to carry ?type=legacy), so the user saw 0 on the first
    // click and a real balance only after switching to the cashaddr card.
    //
    // Fix: send each address VERBATIM (haskoin accepts legacy, cashaddr, and
    // cashaddr with the bitcoincash: prefix) and match the reply BY POSITION.
    // haskoin returns exactly one entry per input, in input order, with zeros
    // for never-used addresses — verified against the live API for legacy,
    // cashaddr and mixed batches. No case folding, so no format is corrupted,
    // and the value shape is kept byte-for-byte identical to the original.
    var BCH_BATCH_URL = (BC.prototype && BC.prototype.BCH_BALANCE_API) ||
      'https://api.haskoin.com/bch/address/balances?addresses=';
    BC.fetchBitcoinCashBalancesBatch = async function (addresses, opts) {
      opts = opts || {};
      var out = new Map();
      if (this.isBot) return out;
      if (!addresses || addresses.length === 0) return out;

      // ── LEGACY (1...) view → real BITCOIN balance ──────────────────────
      // A Bitcoin Cash "legacy" address (e.g. 1BgGZ9tcN4rm…) is a byte-for-byte
      // P2PKH base58 string — the SAME text is a valid *Bitcoin* address. On the
      // CashAddr (q…) view we report the BCH-chain balance (correct for Bitcoin
      // Cash). But on the legacy view the user must see what a Bitcoin explorer
      // shows for that 1… address: its BITCOIN balance — NOT the BCH balance of
      // the same hash160. BTC and BCH diverged in 2017, so for 1BgGZ9tcN4rm… the
      // numbers genuinely differ (BTC: 197 tx / recv 0.25001029 ; BCH: 59 tx /
      // recv 0.52318415). Reporting the BCH number on a 1… address is what the
      // user (rightly) called fake — it never matches a Bitcoin explorer.
      // So when the page is rendering the legacy format, defer to the engine's
      // OWN Bitcoin balance method — the exact one /private-keys/bitcoin uses.
      // Return shape is byte-identical (balance/balanceStr/symbol/txCount/
      // received, symbol 'BTC'), so the grid renders unchanged.
      try {
        var cfg = window.CGT_CONFIG;
        if (cfg && cfg.type === 'legacy' && typeof this.fetchBitcoinBalancesBatch === 'function') {
          return await this.fetchBitcoinBalancesBatch(addresses, opts);
        }
      } catch (eLegacy) { /* fall through to the BCH (cashaddr) path below */ }

      var self = this;
      var onProgress = opts.onProgress || null;
      var done = 0;
      var BATCH = 50;
      var base = (self.BCH_BALANCE_API || BCH_BATCH_URL);

      function emptyVal() { return { balance: 0n, balanceStr: '0', symbol: 'BCH', txCount: 0, received: '0' }; }

      for (var i = 0; i < addresses.length; i += BATCH) {
        var slice = addresses.slice(i, i + BATCH);
        var arr = null;
        try {
          // Send addresses exactly as rendered — do NOT lowercase.
          var resp = await self.fetchWithTimeout(base + encodeURIComponent(slice.join(',')), { method: 'GET' }, 15000);
          if (resp.ok) {
            var data = await resp.json();
            if (Array.isArray(data)) arr = data;
          }
        } catch (e) { /* leave arr null -> honest zeros for this slice */ }

        slice.forEach(function (addr, k) {
          var val;
          // Position match first (haskoin preserves input order); this is
          // format-independent so it works for legacy AND cashaddr inputs.
          var row = (arr && arr.length === slice.length) ? arr[k] : null;
          if (!row && arr) {
            // Defensive: if the array length ever differs, fall back to
            // matching by the cashaddr the API echoes back.
            var want = addr.toLowerCase().replace('bitcoincash:', '');
            for (var r = 0; r < arr.length; r++) {
              var got = (arr[r] && arr[r].address ? arr[r].address : '').toLowerCase().replace('bitcoincash:', '');
              if (got === want) { row = arr[r]; break; }
            }
          }
          if (row) {
            var sats = (row.confirmed || 0) + (row.unconfirmed || 0);
            var recv = row.received || 0;
            val = {
              balance: BigInt(sats),
              balanceStr: (sats / 1e8).toFixed(8),
              symbol: 'BCH',
              txCount: row.txs || 0,
              received: (recv / 1e8).toFixed(8)
            };
          } else {
            val = emptyVal();
          }
          out.set(addr, val);
          if (onProgress) { try { onProgress(addr, val, done, addresses.length); } catch (e6) {} }
          done++;
        });

        if (i + BATCH < addresses.length) await this.sleep(200);
      }
      return out;
    };

    try { console.log('[balance-fix] SUI/XRP/ZEC/SOL/BCH balance methods patched'); } catch (e) {}
  }

  // BalanceChecker is defined synchronously by the deferred balance-checker.obf.js
  // that precedes us; poll briefly in case of any load-order surprise.
  if (window.BalanceChecker) {
    patch(window.BalanceChecker);
  } else {
    var tries = 0;
    var iv = setInterval(function () {
      if (window.BalanceChecker) { clearInterval(iv); patch(window.BalanceChecker); }
      else if (++tries > 100) { clearInterval(iv); }
    }, 50);
  }
})();

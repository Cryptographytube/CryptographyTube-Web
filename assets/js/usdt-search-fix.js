/*!
 * usdt-search-fix.js — REAL USDT (Tether) token balance in the global Wallet Search.
 *
 * Why this file exists
 * --------------------
 * The Ctrl+K "Wallet Search" (window.WalletSearch) derives an address for every
 * enabled chain in CGT_CONFIG.chains and fetches its balance in
 * checkChainBalances(key, chainObj). That method dispatches ONLY on
 * chainObj.type — and USDT's config type is "tron" (it reuses the Tron address),
 * so the USDT card fell through to BalanceChecker.fetchTronBalancesBatch and
 * showed the native TRX balance (e.g. "104.297631 TRX") instead of the real
 * USDT TRC-20 token balance (e.g. "1000 USDT"). The chain KEY ("usdt") is known
 * at that point but was never used, and USDT shares the exact Tron address with
 * the real Tron card, so the two cannot be told apart at the BalanceChecker
 * layer — the fix has to live where the key is visible: checkChainBalances.
 *
 * What it does
 * ------------
 *   1. Guarantees CGT_CONFIG.chains.usdt exists + enabled, so the USDT card
 *      shows up in the results grid on EVERY page (some pages omitted it).
 *   2. Wraps window.WalletSearch.checkChainBalances: for the USDT chain it
 *      fetches the real token balance via the SAME on-chain multicall contracts
 *      /private-keys/usdt uses — balances(address[] users, address[] tokens):
 *        TRC-20 -> 41856001…afc7 over TronGrid triggerconstantcontract,
 *        ERC-20 -> 0xDe3d…955d  over public Ethereum JSON-RPC (eth_call),
 *      passing the USDT contract as the token — then renders "N USDT" into the
 *      card, per-address cells and summary exactly like every other chain
 *      (ws-balance-usdt / ws-addr-bal-usdt-* / ws-status-usdt + has-balance /
 *      has-activity / Active). Every other chain is untouched (orig is called).
 *
 * Self-contained (the encoding/fetch helpers are copied verbatim from the
 * shipped, ground-truth-verified usdt-balance.js). Loaded with `defer`
 * immediately after balance-fix.js; polls briefly for window.WalletSearch
 * (created by app.obf.js) so load order never matters.
 */
(function () {
  'use strict';
  if (window.__usdtSearchFix) return;
  window.__usdtSearchFix = true;

  /* ------------------------------------------------------------ config --- */
  var USDT_ERC20 = '0xdac17f958d2ee523a2206206994597c13d831ec7';
  var USDT_TRC20_HEX = '41a614f803b6fd780986a42c78ec9c7f77e6ded13c';
  var EVM_CHECKER = '0xDe3d4d3BdF0a0d948AA3CD030E77120d49f9955d';   // balances(users,tokens)
  var TRON_CHECKER_HEX = '41856001c68f53200cfa0bec38fc08ba8fd94bafc7'; // balances(users,tokens)
  var ETH_RPCS = [
    'https://ethereum-rpc.publicnode.com',
    'https://cloudflare-eth.com',
    'https://eth.llamarpc.com',
    'https://rpc.ankr.com/eth'
  ];
  var TRON_APIS = ['https://api.trongrid.io'];
  var DECIMALS = 6;          // USDT uses 6 decimals on both Tron and Ethereum
  var BATCH = 100;           // addresses per multicall
  var ZERO_TRON = '410000000000000000000000000000000000000000';

  var USDT_CHAIN = {
    name: 'USDT', symbol: 'USDT', logo: 'usdt', iconType: 'solid',
    iconName: 'dollar-sign', color: '#26a17b', type: 'tron',
    explorer: 'https://tronscan.org/#/address/', enabled: true
  };

  /* ----------------------------------------------------------- helpers --- */
  function pad32(x) { return x.padStart(64, '0'); }
  function stripHex(a) { return (a || '').toLowerCase().replace(/^0x/, ''); }

  // Format integer base units (6 decimals) as a trimmed decimal string.
  function fmt(v) {
    v = (typeof v === 'bigint') ? v : BigInt(v || 0);
    var base = 10n ** BigInt(DECIMALS);
    var whole = (v / base).toString();
    var frac = (v % base).toString().padStart(DECIMALS, '0').replace(/0+$/, '');
    return frac ? (whole + '.' + frac) : whole;
  }

  // ABI-encode balances(address[] users, address[] tokens) for an EVM eth_call.
  function encBalancesEvm(users, tokens) {
    var sel = 'f0002ea9';
    var usersOff = 0x40, tokensOff = 0x40 + 0x20 + users.length * 0x20;
    var d = sel + pad32(usersOff.toString(16)) + pad32(tokensOff.toString(16));
    d += pad32(users.length.toString(16));
    users.forEach(function (u) { d += pad32(stripHex(u)); });
    d += pad32(tokens.length.toString(16));
    tokens.forEach(function (t) { d += pad32(stripHex(t)); });
    return '0x' + d;
  }

  // Same call for TronGrid's `parameter` field: strip the leading 0x41 version
  // byte from every 21-byte Tron address, no function selector.
  function encBalancesTron(users, tokens) {
    function strip(a) { a = (a || '').toLowerCase().replace(/^0x/, ''); return a.indexOf('41') === 0 ? a.slice(2) : a; }
    var usersOff = 0x40, tokensOff = 0x40 + 0x20 + users.length * 0x20;
    var d = pad32(usersOff.toString(16)) + pad32(tokensOff.toString(16));
    d += pad32(users.length.toString(16));
    users.forEach(function (u) { d += pad32(strip(u)); });
    d += pad32(tokens.length.toString(16));
    tokens.forEach(function (t) { d += pad32(strip(t)); });
    return d;
  }

  // Decode a uint256[] returned by balances(): [offset][count][v0][v1]…
  function decodeBalances(hex) {
    hex = (hex || '').replace(/^0x/, '');
    if (!hex || hex.length < 0x80) return [];
    var count = parseInt(hex.substring(0x40, 0x80), 16) || 0;
    var out = [];
    for (var i = 0; i < count; i++) {
      var s = 0x80 + i * 0x40;
      var word = hex.substring(s, s + 0x40);
      out.push(word ? BigInt('0x' + word) : 0n);
    }
    return out;
  }

  // Base58Check-decode a Tron address to its hex form (0x41 + 20-byte hash).
  var B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
  function b58decode(s) {
    var num = 0n;
    for (var i = 0; i < s.length; i++) {
      var idx = B58.indexOf(s[i]);
      if (idx < 0) return null;
      num = num * 58n + BigInt(idx);
    }
    var hex = num.toString(16);
    if (hex.length % 2) hex = '0' + hex;
    var zeros = 0;
    for (var j = 0; j < s.length && s[j] === '1'; j++) zeros++;
    return '00'.repeat(zeros) + hex;
  }
  function tronToHex(addr) {
    if (!addr) return null;
    if (addr.indexOf('41') === 0 && addr.length === 42) return addr.toLowerCase();
    var full = b58decode(addr);
    if (!full || full.length < 8) return null;
    return full.slice(0, full.length - 8).toLowerCase(); // drop 4-byte checksum
  }

  function fetchWithTimeout(url, opts, ms) {
    return new Promise(function (resolve, reject) {
      var ctrl = new AbortController();
      var timer = setTimeout(function () { ctrl.abort(); reject(new Error('timeout')); }, ms || 15000);
      opts = opts || {}; opts.signal = ctrl.signal;
      fetch(url, opts).then(
        function (r) { clearTimeout(timer); resolve(r); },
        function (e) { clearTimeout(timer); reject(e); }
      );
    });
  }

  /* --------------------------------------------------- balance fetchers --- */
  // ERC-20: Map(lowercased 0x-address -> BigInt base units)
  async function fetchErc20(addresses) {
    var out = new Map();
    for (var i = 0; i < addresses.length; i += BATCH) {
      var slice = addresses.slice(i, i + BATCH);
      var users = slice.map(function (a) { return a || '0x0000000000000000000000000000000000000000'; });
      var data = encBalancesEvm(users, [USDT_ERC20]);
      var result = null;
      for (var r = 0; r < ETH_RPCS.length && !result; r++) {
        try {
          var resp = await fetchWithTimeout(ETH_RPCS[r], {
            method: 'POST', headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ jsonrpc: '2.0', id: 1, method: 'eth_call', params: [{ to: EVM_CHECKER, data: data }, 'latest'] })
          }, 15000);
          var j = await resp.json();
          if (j && j.result && j.result !== '0x') result = j.result;
        } catch (e) { /* try next RPC */ }
      }
      var vals = result ? decodeBalances(result) : [];
      slice.forEach(function (a, k) { out.set((a || '').toLowerCase(), vals[k] != null ? vals[k] : 0n); });
    }
    return out;
  }

  // TRC-20: Map(base58 T-address -> BigInt base units)
  async function fetchTrc20(addresses) {
    var out = new Map();
    for (var i = 0; i < addresses.length; i += BATCH) {
      var slice = addresses.slice(i, i + BATCH);
      var users = slice.map(function (a) { return tronToHex(a) || ZERO_TRON; });
      var param = encBalancesTron(users, [USDT_TRC20_HEX]);
      var result = null;
      for (var a = 0; a < TRON_APIS.length && !result; a++) {
        try {
          var resp = await fetchWithTimeout(TRON_APIS[a] + '/wallet/triggerconstantcontract', {
            method: 'POST', headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({
              owner_address: ZERO_TRON, contract_address: TRON_CHECKER_HEX,
              function_selector: 'balances(address[],address[])', parameter: param, visible: false
            })
          }, 15000);
          var j = await resp.json();
          if (j && j.constant_result && j.constant_result[0]) result = '0x' + j.constant_result[0];
        } catch (e) { /* try next API */ }
      }
      var vals = result ? decodeBalances(result) : [];
      slice.forEach(function (addr, k) { out.set(addr, vals[k] != null ? vals[k] : 0n); });
    }
    return out;
  }

  /* --------------------------------------------------- USDT chain render --- */
  function isUsdtChain(key, chainObj) {
    if (key === 'usdt') return true;
    return !!(chainObj && String(chainObj.symbol || '').toUpperCase() === 'USDT');
  }

  // Mirror of the engine's checkChainBalances DOM/counter contract, but with
  // real USDT token balances and "USDT" units. Called INSTEAD of the original
  // for the USDT card, so no TRX ever flashes and no wasted native call is made.
  async function checkUsdtChain(WS, key, chainObj) {
    var addrObjs = (chainObj && chainObj.addresses) || [];
    var statusEl = document.getElementById('ws-status-' + key);
    var total = addrObjs.length, checked = 0;
    function tick() { if (statusEl) statusEl.textContent = checked + '/' + total; }

    var all = addrObjs.map(function (a) { return a.address; });
    var tronAddrs = all.filter(function (a) { return /^T[1-9A-HJ-NP-Za-km-z]{25,40}$/.test(a); });
    var evmAddrs = all.filter(function (a) { return /^0x[0-9a-fA-F]{40}$/.test(a); });

    var balMap = new Map();   // address -> BigInt (base units)
    var hadError = false;
    if (tronAddrs.length) {
      try { (await fetchTrc20(tronAddrs)).forEach(function (v, k) { balMap.set(k, v); }); }
      catch (e) { hadError = true; }
    }
    if (evmAddrs.length) {
      try { (await fetchErc20(evmAddrs)).forEach(function (v, k) { balMap.set(k, v); }); }  // keys lowercased
      catch (e) { hadError = true; }
    }

    var chainTotal = 0n, chainActive = false;
    addrObjs.forEach(function (a) {
      checked++; tick();
      var raw = balMap.has(a.address) ? balMap.get(a.address) : balMap.get((a.address || '').toLowerCase());
      if (raw == null) raw = 0n;
      chainTotal += raw;
      if (raw > 0n) chainActive = true;

      var sanitized = (a.address || '').replace(/[^a-zA-Z0-9]/g, '');
      var cell = document.getElementById('ws-addr-bal-' + key + '-' + sanitized);
      if (cell) {
        cell.classList.remove('has-error');
        cell.textContent = fmt(raw) + ' USDT';
        cell.classList.toggle('has-balance', raw > 0n);
      }
      var item = document.querySelector('.ws-address-item[data-chain="' + key + '"][data-address="' + a.address + '"]');
      if (item && raw > 0n) {
        item.classList.add('has-balance');
        item.classList.add('has-activity');
        WS.activeAddressCount = (WS.activeAddressCount || 0) + 1;
      }
    });

    var card = document.getElementById('ws-chain-' + key);
    if (card) {
      if (chainTotal > 0n) card.classList.add('has-balance');
      if (hadError) card.classList.add('has-error');
      if (chainActive) {
        card.classList.add('has-activity');
        WS.activeChainCount = (WS.activeChainCount || 0) + 1;
        try {
          if (!WS.savedToFound) {
            WS.savedToFound = true;
            var inputEl = document.getElementById('walletSearchInput');
            var inputVal = inputEl && inputEl.value && inputEl.value.trim();
            if (inputVal && WS.inputType && window.FoundWallets) {
              var st = WS.inputType === 'mnemonic' ? 'mnemonic'
                     : WS.inputType === 'brainwallet' ? 'brainwallet' : 'private-key';
              var extra = {};
              if (WS.inputType === 'brainwallet' && WS.privateKeyHex) extra.hex = WS.privateKeyHex;
              window.FoundWallets.save(st, inputVal, extra);
            }
          }
        } catch (e) { /* found-wallets save is best-effort */ }
      }
    }

    var balEl = document.getElementById('ws-balance-' + key);
    if (balEl) {
      if (hadError && chainTotal === 0n) {
        balEl.textContent = 'RPC Error';
        balEl.classList.add('has-error');
      } else {
        balEl.textContent = fmt(chainTotal) + ' USDT';
        if (chainTotal > 0n) balEl.classList.add('has-balance');
      }
    }
    if (statusEl) {
      statusEl.textContent = hadError && chainTotal === 0n ? 'All RPCs failed' : (chainActive ? 'Active' : 'No activity');
      statusEl.classList.toggle('active', chainActive);
    }
    WS.checkedChainCount = (WS.checkedChainCount || 0) + 1;
    if (typeof WS.updateSummary === 'function') { try { WS.updateSummary(); } catch (e) {} }
  }

  /* ----------------------------------------------------------- install --- */
  function ensureUsdtConfig() {
    try {
      var cfg = window.CGT_CONFIG;
      if (!cfg) return;
      cfg.chains = cfg.chains || {};
      if (!cfg.chains.usdt) {
        var o = {}; for (var k in USDT_CHAIN) o[k] = USDT_CHAIN[k];
        cfg.chains.usdt = o;
      } else if (cfg.chains.usdt.enabled === false) {
        cfg.chains.usdt.enabled = true;
      }
    } catch (e) {}
  }

  function patch(WS) {
    if (!WS || WS.__usdtSearchPatched) return false;
    if (typeof WS.checkChainBalances !== 'function') return false;
    WS.__usdtSearchPatched = true;
    var orig = WS.checkChainBalances;
    WS.checkChainBalances = async function (key, chainObj) {
      if (isUsdtChain(key, chainObj)) {
        try { return await checkUsdtChain(this, key, chainObj); }
        catch (e) { try { return await orig.call(this, key, chainObj); } catch (e2) {} }
      }
      return orig.call(this, key, chainObj);
    };
    try { console.log('[usdt-search-fix] WalletSearch USDT balance patched'); } catch (e) {}
    return true;
  }

  function install() {
    ensureUsdtConfig();
    return patch(window.WalletSearch);
  }

  if (!install()) {
    var tries = 0;
    var iv = setInterval(function () {
      if (install() || ++tries > 200) clearInterval(iv);
    }, 25);
  }
  // CGT_CONFIG may be assigned after us on some pages; re-run the config guard once more.
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', ensureUsdtConfig);
  }
})();

/*!
 * usdt-balance.js — REAL USDT (Tether) token balances for private-keys/usdt.html
 *
 * Why this file exists
 * --------------------
 * USDT is a *token*, not a base chain, so it has no native key derivation: the
 * page reuses the host chain's addresses (TRC-20 `T...` on Tron, ERC-20 `0x...`
 * on Ethereum) and reports the USDT contract balance for each.
 *
 * The engine dispatches balance-checking by the page's chain SLUG
 * (config.chain). For every real chain that slug matches a branch in
 * BalanceChecker/CGT.fetchBalancesForPage(); for "usdt" it matches NONE, so the
 * balance column stayed on its loading spinner forever ("waiting"). This patch
 * fixes exactly that.
 *
 * What it does
 * ------------
 * Overrides CGT.fetchBalancesForPage() on the USDT page with a self-contained
 * implementation that:
 *   1. reads every rendered .key-row address,
 *   2. batches them through the SAME on-chain multicall contracts the site
 *      already uses — passing the USDT contract as the token instead of the
 *      native sentinel:
 *        ERC-20  -> 0xDe3d…955d  balances(address[] users, address[] tokens)
 *                   over public Ethereum JSON-RPC (eth_call),
 *        TRC-20  -> 41856001…afc7 balances(address[],address[]) over TronGrid
 *                   triggerconstantcontract,
 *   3. writes "N USDT" into each .col-balance cell and the #totalBalance /
 *      #activeWallets summary, matching the site's exact DOM so styling,
 *      the active/inactive status icon and the has-balance highlight are
 *      identical to every other chain.
 *
 * Network (Tron vs Ethereum) follows the page's own ?type= toggle, read from
 * window.CGT_CONFIG.chainInfo.type ("tron" | "evm"). Verified against USDT
 * ground-truth balanceOf() on both chains before shipping.
 *
 * Loaded with `defer` alongside the other balance patches; it polls briefly for
 * window.CGT (created by app.obf.js) and installs before the first render.
 */
(function () {
  'use strict';

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
  var POLL_MS = 25, MAX_TRIES = 400, GRACE_TRIES = 12;   // install poll; 12*25ms≈300ms heal grace

  function config() { return window.CGT_CONFIG || {}; }
  function network() {
    var t = (config().chainInfo && config().chainInfo.type) || 'tron';
    return t === 'evm' ? 'ethereum' : 'tron';
  }

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

  // ABI-encode the same call for TronGrid's `parameter` field: strip the leading
  // 0x41 version byte from every 21-byte Tron address, no function selector.
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

  // Pull a clean address out of a cell's text, tolerant of surrounding markup.
  function extractAddress(text, net) {
    text = (text || '').trim();
    var m = (net === 'ethereum')
      ? text.match(/0x[0-9a-fA-F]{40}/)
      : text.match(/T[1-9A-HJ-NP-Za-km-z]{25,40}/);
    return m ? m[0] : '';
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

  /* -------------------------------------------------- loading spinner --- */
  function sleep(ms) { return new Promise(function (r) { setTimeout(r, ms); }); }
  var MIN_SPIN_MS = 450;                       // keep the spinner perceptible on fast/instant renders
  function minSpin(t0) { var el = Date.now() - t0; return el < MIN_SPIN_MS ? sleep(MIN_SPIN_MS - el) : Promise.resolve(); }
  var SPINNER_HTML = '<img src="/assets/svgs/solid/spinner.svg" class="fa-icon fa-spin" width="14" height="14" alt="">';
  // Paint the loading spinner into every balance cell + the summary counters,
  // exactly like the engine does for the built-in chains. We replaced the
  // engine's fetchBalancesForPage (which used to call showLoadingState), so on
  // pagination / random nothing showed the spinner anymore — this restores it.
  // Reuses the engine's own showLoadingState when present so the icon matches.
  function showSpinners(rows) {
    if (window.CGT && typeof window.CGT.showLoadingState === 'function') {
      try { window.CGT.showLoadingState(rows); return; } catch (e) {}
    }
    rows.forEach(function (row) {
      var cell = row.querySelector('.col-balance');
      if (cell) { cell.innerHTML = SPINNER_HTML; cell.classList.remove('has-balance'); }
    });
    var tb = document.getElementById('totalBalance'); if (tb) tb.innerHTML = SPINNER_HTML;
    var aw = document.getElementById('activeWallets'); if (aw) aw.innerHTML = SPINNER_HTML;
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

  /* ---------------------------------------------------------- rendering --- */
  function renderCell(row, raw) {
    var cell = row.querySelector('.col-balance');
    if (!cell) return;
    var has = raw > 0n;
    cell.innerHTML =
      '<span class="balance-info">\n' +
      '                    <span class="bal' + (has ? ' has-balance' : '') + '">' + fmt(raw) + ' USDT</span>\n' +
      '                    <img src="/assets/svgs/solid/circle-check.svg" class="status-icon ' + (has ? 'active' : 'inactive') + '" alt="">\n' +
      '                </span>';
  }

  function updateSummary(total, activeCount) {
    var t = document.getElementById('totalBalance');
    if (t) t.textContent = fmt(total) + ' USDT';
    var a = document.getElementById('activeWallets');
    if (a) a.textContent = String(activeCount);
  }

  /* --------------------------------------------------------------- run --- */
  async function run() {
    var kc = document.getElementById('keysContainer');
    if (!kc) return;
    var rows = Array.prototype.slice.call(kc.querySelectorAll('.key-row'));
    if (!rows.length) return;

    showSpinners(rows);              // visible loading state on every (re)render, like other chains
    var t0 = Date.now();

    var net = network();
    var addrs = rows.map(function (r) {
      var a = r.querySelector('.col-address');
      return extractAddress(a ? a.textContent : '', net);
    });

    var balMap;
    try {
      balMap = (net === 'ethereum') ? await fetchErc20(addrs) : await fetchTrc20(addrs);
    } catch (e) {
      console.error('[usdt-balance] fetch failed', e);
      balMap = new Map();
    }

    await minSpin(t0);               // keep the spinner visible for a beat even if the fetch was instant

    var total = 0n, active = 0;
    rows.forEach(function (row, i) {
      var key = (net === 'ethereum') ? (addrs[i] || '').toLowerCase() : addrs[i];
      var raw = balMap.get(key);
      if (raw == null) raw = 0n;
      total += raw;
      if (raw > 0n) active++;
      renderCell(row, raw);
    });
    updateSummary(total, active);
  }

  /* ---------------------------------------------- render orchestration --- */
  // Serialize renders: the engine's own fetchBalancesForPage call and the
  // initial-load heal below must never fetch concurrently or twice.
  var running = false, renderedOnce = false;
  async function runGuarded() {
    if (running) return;
    running = true;
    try {
      var kc = document.getElementById('keysContainer');
      var hadRows = !!(kc && kc.querySelector('.key-row'));
      await run();
      if (hadRows) renderedOnce = true;
    } catch (e) { try { console.error('[usdt-balance]', e); } catch (_) {} }
    finally { running = false; }
  }

  // A .col-balance cell still showing the engine's loading spinner (or empty)
  // means no real value has been rendered into it yet.
  function spinnerPresent(kc) {
    var cells = kc.querySelectorAll('.col-balance');
    for (var i = 0; i < cells.length; i++) {
      var h = cells[i].innerHTML || '';
      if (!h.trim() || /fa-spin|spinner\.svg/i.test(h)) return true;
    }
    return false;
  }

  // Load-order safety net. usdt-balance.js is deferred BEFORE app.obf.js, so
  // window.CGT (hence our override) can be absent when the engine runs its first
  // fetchBalancesForPage. That original has no branch for the "usdt" chain, so
  // showLoadingState() paints a spinner it never clears. Once rows exist and a
  // short grace has passed without us rendering, heal the column ourselves.
  // Guarded + grace-delayed so the normal path (engine drives our override)
  // never causes a duplicate fetch.
  function kickInitialRender() {
    var tries = 0;
    var iv = setInterval(function () {
      if (++tries > MAX_TRIES) { clearInterval(iv); return; }
      var kc = document.getElementById('keysContainer');
      var rows = kc && kc.querySelectorAll('.key-row');
      if (!rows || !rows.length) return;                          // wait for first render
      if (renderedOnce || running) { clearInterval(iv); return; } // engine drove it
      if (tries < GRACE_TRIES) return;                            // give the engine a moment
      clearInterval(iv);
      if (spinnerPresent(kc)) runGuarded();                       // leftover spinner → heal
    }, POLL_MS);
  }

  /* ----------------------------------------------------------- install --- */
  function install() {
    if (!window.CGT || window.CGT.__usdtBalance) return !!(window.CGT && window.CGT.__usdtBalance);
    window.CGT.__usdtBalance = true;
    // Replace the no-op-for-"usdt" dispatcher with our token-balance fetcher.
    // Called by the engine after every render (initial load AND in-place
    // pagination), so balances refresh on each page.
    window.CGT.fetchBalancesForPage = async function () { await runGuarded(); };
    kickInitialRender();
    try { console.log('[usdt-balance] installed (network:', network() + ')'); } catch (e) {}
    return true;
  }

  /* ------------------------------------------------------------ export --- */
  // The address-database usdt page runs its own tiny page engine and never
  // calls CGT.fetchBalancesForPage, so publish the proven token fetchers for it
  // to drive directly. Without this the page fell back to the host chain's
  // native balance (TRX) in the "USDT Balance" column.
  window.CGT_USDT_TOKEN = {
    network: network,
    fetchErc20: fetchErc20,
    fetchTrc20: fetchTrc20,
    fmt: fmt,
    extractAddress: extractAddress,
    decimals: DECIMALS
  };

  if (!install()) {
    var tries = 0;
    var iv = setInterval(function () {
      if (install() || ++tries > MAX_TRIES) clearInterval(iv);
    }, POLL_MS);
  }
})();

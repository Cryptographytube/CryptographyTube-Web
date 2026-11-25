<?php
/* ============================================================================
   luck-verify.php  —  independent, server-side on-chain verification for the
   "Found Luck" store. Shared by found.php (the browser POST gate) and
   found-purge.php (one-time cleanup of already-stored records).

   THE ONE JOB
     Given (chain, address), ask that chain's OWN public API whether the address
     has any REAL activity, and return server-measured numbers:

        luck_verify_activity($chain, $address) => array(
            'status' => 'active' | 'inactive' | 'unverified',
            'bal'    => decimal string   (real on-chain balance, human units)
            'recv'   => decimal string   ('' where the chain can't report it)
            'tx'     => integer string   ('' where the chain can't report it)
        )

     'active'      the API confirmed balance > 0 OR received > 0 OR tx > 0
     'inactive'    the API confirmed the address is empty (0 / 0 / 0)
     'unverified'  the API failed, or the chain cannot be verified from an
                   address alone (monero, shielded zcash). NEVER guessed.

   FAIL-CLOSED, ON PURPOSE
     A record is saved ONLY on 'active'. 'inactive' and 'unverified' are never
     saved. This is deliberate: the whole point is that a fabricated balance can
     never land on the board. A genuine hit is ~1 in 2^160, so "save nothing we
     can't independently confirm" is exactly right — it cannot invent a finding.

   Numbers are carried as decimal STRINGS (256-bit balances overflow a PHP int),
   so there is no float and no precision loss.
   ============================================================================ */

if (!defined('LUCK_VERIFY_INCLUDED')) {
    define('LUCK_VERIFY_INCLUDED', 1);

/* ------------------------------------------------------------------ HTTP ---- */
if (!function_exists('lv_http')) {
    function lv_http($url, $method = 'GET', $body = null, $headers = array(), $timeout = 15) {
        $timeout = min((int) $timeout, 9);          // bound the browser hot-path (worst case ~2x this)
        $attempts = 0;
        while ($attempts < 2) {                     // one quick retry on a transient failure
            $attempts++;
            if (function_exists('curl_init')) {
                $ch = curl_init($url);
                curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
                curl_setopt($ch, CURLOPT_TIMEOUT, $timeout);
                curl_setopt($ch, CURLOPT_CONNECTTIMEOUT, 6);
                curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
                curl_setopt($ch, CURLOPT_MAXREDIRS, 3);
                curl_setopt($ch, CURLOPT_USERAGENT, 'CGT-LuckVerify/1.0');
                if ($method === 'POST') {
                    curl_setopt($ch, CURLOPT_POST, true);
                    curl_setopt($ch, CURLOPT_POSTFIELDS, (string) $body);
                }
                if ($headers) { curl_setopt($ch, CURLOPT_HTTPHEADER, $headers); }
                $out  = curl_exec($ch);
                $code = (int) curl_getinfo($ch, CURLINFO_HTTP_CODE);
                curl_close($ch);
                if ($out !== false && $code >= 200 && $code < 300) { return $out; }
            } elseif (ini_get('allow_url_fopen')) {
                $opt = array('http' => array(
                    'method'        => $method,
                    'timeout'       => $timeout,
                    'ignore_errors' => true,
                    'header'        => array_merge(array('User-Agent: CGT-LuckVerify/1.0'), $headers),
                ));
                if ($method === 'POST') {
                    $opt['http']['content'] = (string) $body;
                    $opt['http']['header'][] = 'Content-Type: application/json';
                }
                $out = @file_get_contents($url, false, stream_context_create($opt));
                if ($out !== false) { return $out; }
            } else {
                return null;                        // no way to reach the network
            }
            if ($attempts < 2) { usleep(400000); }  // 0.4s before the single retry
        }
        return null;
    }
}
if (!function_exists('lv_json')) {
    function lv_json($url, $method = 'GET', $body = null, $headers = array(), $timeout = 15) {
        $raw = lv_http($url, $method, $body, $headers, $timeout);
        if ($raw === null) { return null; }
        $j = @json_decode($raw, true);
        return is_array($j) ? $j : null;
    }
}

/* -------------------------------------------------------------- DECIMALS ---- */
if (!function_exists('lv_dec_mul_small')) {
    function lv_dec_mul_small($s, $m) {
        $carry = 0; $out = '';
        for ($i = strlen($s) - 1; $i >= 0; $i--) {
            $p = (ord($s[$i]) - 48) * $m + $carry;
            $out = chr(48 + ($p % 10)) . $out;
            $carry = intdiv($p, 10);
        }
        while ($carry > 0) { $out = chr(48 + ($carry % 10)) . $out; $carry = intdiv($carry, 10); }
        $out = ltrim($out, '0');
        return $out === '' ? '0' : $out;
    }
}
if (!function_exists('lv_dec_add_small')) {
    function lv_dec_add_small($s, $a) {
        $carry = $a; $out = '';
        for ($i = strlen($s) - 1; $i >= 0; $i--) {
            $p = (ord($s[$i]) - 48) + $carry;
            $out = chr(48 + ($p % 10)) . $out;
            $carry = intdiv($p, 10);
        }
        while ($carry > 0) { $out = chr(48 + ($carry % 10)) . $out; $carry = intdiv($carry, 10); }
        $out = ltrim($out, '0');
        return $out === '' ? '0' : $out;
    }
}
/* hex string -> decimal-digits string (no 0x, case-insensitive) */
if (!function_exists('lv_hex_to_dec')) {
    function lv_hex_to_dec($hex) {
        $hex = strtolower(trim((string) $hex));
        if (strncmp($hex, '0x', 2) === 0) { $hex = substr($hex, 2); }
        $hex = ltrim($hex, '0');
        if ($hex === '') { return '0'; }
        $dec = '0';
        for ($i = 0; $i < strlen($hex); $i++) {
            $d = strpos('0123456789abcdef', $hex[$i]);
            if ($d === false) { return '0'; }
            $dec = lv_dec_add_small(lv_dec_mul_small($dec, 16), $d);
        }
        return $dec;
    }
}
/* integer-units digits -> human decimal string (scale = decimals of the unit) */
if (!function_exists('lv_units_to_dec')) {
    function lv_units_to_dec($units, $scale) {
        $units = (string) $units;
        if (!preg_match('/^[0-9]+$/', $units)) { return '0'; }
        $units = ltrim($units, '0');
        if ($units === '') { $units = '0'; }
        if ($scale <= 0) { return $units; }
        $units = str_pad($units, $scale + 1, '0', STR_PAD_LEFT);
        $int  = substr($units, 0, -$scale);
        $frac = rtrim(substr($units, -$scale), '0');
        return $frac === '' ? $int : $int . '.' . $frac;
    }
}
/* true when a pure-digit units string is > 0 */
if (!function_exists('lv_units_pos')) {
    function lv_units_pos($units) {
        return (bool) preg_match('/[1-9]/', (string) $units);
    }
}
/* normalize a decimal string; blank/garbage -> '' so callers can drop it */
if (!function_exists('lv_norm_int')) {
    function lv_norm_int($n) {
        $n = ltrim((string) $n, '+');
        return preg_match('/^[0-9]+$/', $n) ? $n : '0';
    }
}

/* ------------------------------------------------------- chain RPC tables --- */
if (!function_exists('lv_evm_rpc')) {
    function lv_evm_rpc() {
        return array(
            'ethereum'  => 'https://ethereum-rpc.publicnode.com',
            'bnb'       => 'https://bsc-rpc.publicnode.com',
            'polygon'   => 'https://polygon-bor-rpc.publicnode.com',
            'arbitrum'  => 'https://arbitrum-one-rpc.publicnode.com',
            'avalanche' => 'https://avalanche-c-chain-rpc.publicnode.com',
            'optimism'  => 'https://optimism-rpc.publicnode.com',
            'base'      => 'https://base-rpc.publicnode.com',
            'zksync'    => 'https://zksync-era.blockpi.network/v1/rpc/public',
        );
    }
}

/* normalize an EVM address to 0x + 40 lowercase hex, or '' if not valid */
if (!function_exists('lv_evm_addr')) {
    function lv_evm_addr($address) {
        $a = strtolower(trim((string) $address));
        if (strncmp($a, '0x', 2) === 0) { $a = substr($a, 2); }
        return preg_match('/^[0-9a-f]{40}$/', $a) ? ('0x' . $a) : '';
    }
}

/* ============================================================ PER-CHAIN CHECKS
   Each returns one of:
     array('status'=>'active'|'inactive', 'bal'=>.., 'recv'=>.., 'tx'=>..)
     null   -> could not verify (API failure / unsupported) -> 'unverified'   */

/* EVM native coin: balance (wei) + tx count (nonce). 18 decimals. */
if (!function_exists('lv_check_evm_native')) {
    function lv_check_evm_native($rpc, $address) {
        $a = lv_evm_addr($address);
        if ($a === '') { return null; }
        $req = json_encode(array(
            array('jsonrpc' => '2.0', 'id' => 0, 'method' => 'eth_getBalance',          'params' => array($a, 'latest')),
            array('jsonrpc' => '2.0', 'id' => 1, 'method' => 'eth_getTransactionCount',  'params' => array($a, 'latest')),
        ));
        $j = lv_json($rpc, 'POST', $req, array('Content-Type: application/json'), 20);
        if (!is_array($j)) { return null; }
        $balHex = null; $nonceHex = null;
        foreach ($j as $r) {
            if (!isset($r['id'])) { continue; }
            if ((int) $r['id'] === 0) { $balHex   = isset($r['result']) ? $r['result'] : null; }
            if ((int) $r['id'] === 1) { $nonceHex = isset($r['result']) ? $r['result'] : null; }
        }
        if ($balHex === null && $nonceHex === null) { return null; }   // both missing = bad reply
        $wei   = lv_hex_to_dec($balHex);
        $nonce = lv_hex_to_dec($nonceHex);
        $active = lv_units_pos($wei) || lv_units_pos($nonce);
        return array(
            'status' => $active ? 'active' : 'inactive',
            'bal'    => lv_units_to_dec($wei, 18),
            'recv'   => '',
            'tx'     => lv_units_pos($nonce) ? $nonce : '0',
        );
    }
}

/* USDT (ERC-20) on Ethereum: balanceOf(address) + native tx count. 6 decimals. */
if (!function_exists('lv_check_usdt')) {
    function lv_check_usdt($address) {
        $a = lv_evm_addr($address);
        if ($a === '') { return null; }
        $rpc      = 'https://ethereum-rpc.publicnode.com';
        $contract = '0xdac17f958d2ee523a2206206994597c13d831ec7';         // USDT (Tether) mainnet
        $data     = '0x70a08231' . str_pad(substr($a, 2), 64, '0', STR_PAD_LEFT);  // balanceOf(addr)
        $req = json_encode(array(
            array('jsonrpc' => '2.0', 'id' => 0, 'method' => 'eth_call',
                  'params' => array(array('to' => $contract, 'data' => $data), 'latest')),
            array('jsonrpc' => '2.0', 'id' => 1, 'method' => 'eth_getTransactionCount',
                  'params' => array($a, 'latest')),
        ));
        $j = lv_json($rpc, 'POST', $req, array('Content-Type: application/json'), 20);
        if (!is_array($j)) { return null; }
        $balHex = null; $nonceHex = null;
        foreach ($j as $r) {
            if (!isset($r['id'])) { continue; }
            if ((int) $r['id'] === 0) { $balHex   = isset($r['result']) ? $r['result'] : null; }
            if ((int) $r['id'] === 1) { $nonceHex = isset($r['result']) ? $r['result'] : null; }
        }
        if ($balHex === null && $nonceHex === null) { return null; }
        $tok   = lv_hex_to_dec($balHex);       // USDT balance in 6-decimal units
        $nonce = lv_hex_to_dec($nonceHex);
        $active = lv_units_pos($tok) || lv_units_pos($nonce);
        return array(
            'status' => $active ? 'active' : 'inactive',
            'bal'    => lv_units_to_dec($tok, 6),
            'recv'   => '',
            'tx'     => lv_units_pos($nonce) ? $nonce : '0',
        );
    }
}

/* Bitcoin: blockchain.info balance. 8 decimals. */
if (!function_exists('lv_check_bitcoin')) {
    function lv_check_bitcoin($address) {
        $url = 'https://blockchain.info/balance?cors=true&active=' . rawurlencode($address);
        $j = lv_json($url, 'GET', null, array(), 20);
        if (!is_array($j)) { return null; }
        $s = isset($j[$address]) ? $j[$address] : (count($j) ? reset($j) : null);
        if (!is_array($s)) { return null; }
        $bal  = lv_norm_int(isset($s['final_balance'])  ? $s['final_balance']  : 0);
        $recv = lv_norm_int(isset($s['total_received']) ? $s['total_received'] : 0);
        $tx   = (int) (isset($s['n_tx']) ? $s['n_tx'] : 0);
        $active = lv_units_pos($bal) || lv_units_pos($recv) || $tx > 0;
        return array(
            'status' => $active ? 'active' : 'inactive',
            'bal'    => lv_units_to_dec($bal, 8),
            'recv'   => lv_units_to_dec($recv, 8),
            'tx'     => (string) $tx,
        );
    }
}

/* Esplora-style (litecoin). scale decimals. */
if (!function_exists('lv_check_esplora')) {
    function lv_check_esplora($base, $address, $scale) {
        $j = lv_json($base . '/api/address/' . rawurlencode($address), 'GET', null, array(), 15);
        if (!is_array($j)) { return null; }
        $cs = isset($j['chain_stats'])   ? $j['chain_stats']   : array();
        $ms = isset($j['mempool_stats']) ? $j['mempool_stats'] : array();
        $recv = (int) (isset($cs['funded_txo_sum']) ? $cs['funded_txo_sum'] : 0)
              + (int) (isset($ms['funded_txo_sum']) ? $ms['funded_txo_sum'] : 0);
        $spent= (int) (isset($cs['spent_txo_sum'])  ? $cs['spent_txo_sum']  : 0);
        $bal  = $recv - $spent;
        $tx   = (int) (isset($cs['tx_count']) ? $cs['tx_count'] : 0)
              + (int) (isset($ms['tx_count']) ? $ms['tx_count'] : 0);
        $active = $bal > 0 || $recv > 0 || $tx > 0;
        return array(
            'status' => $active ? 'active' : 'inactive',
            'bal'    => lv_units_to_dec((string) max(0, $bal), $scale),
            'recv'   => lv_units_to_dec((string) max(0, $recv), $scale),
            'tx'     => (string) $tx,
        );
    }
}

/* BlockCypher (dogecoin). scale decimals. */
if (!function_exists('lv_check_blockcypher')) {
    function lv_check_blockcypher($base, $address, $scale) {
        $j = lv_json($base . '/addrs/' . rawurlencode($address) . '/balance', 'GET', null, array(), 15);
        if (!is_array($j)) { return null; }
        $bal  = $j['final_balance']  ?? 0;
        $recv = $j['total_received'] ?? 0;
        $tx   = isset($j['final_n_tx']) ? (int) $j['final_n_tx'] : (int) ($j['n_tx'] ?? 0);
        $balS  = is_float($bal)  ? sprintf('%.0f', $bal)  : lv_norm_int($bal);
        $recvS = is_float($recv) ? sprintf('%.0f', $recv) : lv_norm_int($recv);
        $active = lv_units_pos($balS) || lv_units_pos($recvS) || $tx > 0;
        return array(
            'status' => $active ? 'active' : 'inactive',
            'bal'    => lv_units_to_dec($balS, $scale),
            'recv'   => lv_units_to_dec($recvS, $scale),
            'tx'     => (string) $tx,
        );
    }
}

/* Haskoin (bitcoin-cash). scale decimals. */
if (!function_exists('lv_check_haskoin')) {
    function lv_check_haskoin($base, $address, $scale) {
        $j = lv_json($base . '/address/' . rawurlencode($address) . '/balance', 'GET', null, array(), 15);
        if (!is_array($j)) { return null; }
        $bal  = (int) ($j['confirmed'] ?? 0) + (int) ($j['unconfirmed'] ?? 0);
        $recv = (int) ($j['received'] ?? 0);
        $tx   = (int) ($j['txs'] ?? 0);
        $active = $bal > 0 || $recv > 0 || $tx > 0;
        return array(
            'status' => $active ? 'active' : 'inactive',
            'bal'    => lv_units_to_dec((string) max(0, $bal), $scale),
            'recv'   => lv_units_to_dec((string) max(0, $recv), $scale),
            'tx'     => (string) $tx,
        );
    }
}

/* TRON: trongrid account. 6 decimals. */
if (!function_exists('lv_check_tron')) {
    function lv_check_tron($address) {
        $j = lv_json('https://api.trongrid.io/v1/accounts/' . rawurlencode($address), 'GET', null, array(), 15);
        if (!is_array($j) || !isset($j['success'])) { return null; }
        if (empty($j['data']) || !isset($j['data'][0])) {
            return array('status' => 'inactive', 'bal' => '0', 'recv' => '', 'tx' => '0');  // no account = empty
        }
        $d   = $j['data'][0];
        $bal = lv_norm_int(isset($d['balance']) ? $d['balance'] : 0);
        $active = lv_units_pos($bal);
        return array(
            'status' => $active ? 'active' : 'inactive',
            'bal'    => lv_units_to_dec($bal, 6),
            'recv'   => '',
            'tx'     => '',
        );
    }
}

/* XRP: xrplcluster account_info. 6 decimals. */
if (!function_exists('lv_check_xrp')) {
    function lv_check_xrp($address) {
        $req = json_encode(array('method' => 'account_info',
            'params' => array(array('account' => $address, 'ledger_index' => 'validated'))));
        $j = lv_json('https://xrplcluster.com/', 'POST', $req, array('Content-Type: application/json'), 15);
        if (!is_array($j)) { return null; }
        $r = isset($j['result']) ? $j['result'] : array();
        if (isset($r['error']) && $r['error'] === 'actNotFound') {
            return array('status' => 'inactive', 'bal' => '0', 'recv' => '', 'tx' => '0');  // unfunded = empty
        }
        if (isset($r['error'])) { return null; }
        $bal = (isset($r['account_data']['Balance']) && preg_match('/^[0-9]+$/', (string) $r['account_data']['Balance']))
             ? (string) $r['account_data']['Balance'] : '0';
        return array(
            'status' => lv_units_pos($bal) ? 'active' : 'inactive',
            'bal'    => lv_units_to_dec($bal, 6),
            'recv'   => '',
            'tx'     => '',
        );
    }
}

/* Solana: getBalance (+ recent signatures for activity). 9 decimals. */
if (!function_exists('lv_check_solana')) {
    function lv_check_solana($address) {
        $rpc = 'https://api.mainnet-beta.solana.com';
        $req = json_encode(array('jsonrpc' => '2.0', 'id' => 1, 'method' => 'getBalance', 'params' => array($address)));
        $j = lv_json($rpc, 'POST', $req, array('Content-Type: application/json'), 15);
        if (!is_array($j) || !isset($j['result']['value'])) { return null; }
        $lamports = lv_norm_int($j['result']['value']);
        if (lv_units_pos($lamports)) {
            return array('status' => 'active', 'bal' => lv_units_to_dec($lamports, 9), 'recv' => '', 'tx' => '');
        }
        // zero balance: still active if it has any signature history
        $sreq = json_encode(array('jsonrpc' => '2.0', 'id' => 1, 'method' => 'getSignaturesForAddress',
            'params' => array($address, array('limit' => 1))));
        $sj = lv_json($rpc, 'POST', $sreq, array('Content-Type: application/json'), 15);
        if (is_array($sj) && !empty($sj['result'])) {
            return array('status' => 'active', 'bal' => '0', 'recv' => '', 'tx' => '');
        }
        return array('status' => 'inactive', 'bal' => '0', 'recv' => '', 'tx' => '');
    }
}

/* Sui: suix_getBalance (native SUI). 9 decimals (MIST). */
if (!function_exists('lv_check_sui')) {
    function lv_check_sui($address) {
        $req = json_encode(array('jsonrpc' => '2.0', 'id' => 1, 'method' => 'suix_getBalance',
            'params' => array($address, '0x2::sui::SUI')));
        $j = lv_json('https://fullnode.mainnet.sui.io', 'POST', $req, array('Content-Type: application/json'), 15);
        if (!is_array($j) || !isset($j['result']['totalBalance'])) { return null; }
        $mist = lv_norm_int($j['result']['totalBalance']);
        return array(
            'status' => lv_units_pos($mist) ? 'active' : 'inactive',
            'bal'    => lv_units_to_dec($mist, 9),
            'recv'   => '',
            'tx'     => '',
        );
    }
}

/* TON: toncenter address information. 9 decimals (nanoton). */
if (!function_exists('lv_check_ton')) {
    function lv_check_ton($address) {
        $url = 'https://toncenter.com/api/v2/getAddressInformation?address=' . rawurlencode($address);
        $j = lv_json($url, 'GET', null, array(), 15);
        if (!is_array($j) || empty($j['ok']) || !isset($j['result']['balance'])) { return null; }
        $nano = lv_norm_int($j['result']['balance']);
        return array(
            'status' => lv_units_pos($nano) ? 'active' : 'inactive',
            'bal'    => lv_units_to_dec($nano, 9),
            'recv'   => '',
            'tx'     => '',
        );
    }
}

/* Zcash: transparent (t-addr) via Blockchair. 8 decimals. Shielded is opaque. */
if (!function_exists('lv_check_zcash')) {
    function lv_check_zcash($address) {
        // Only transparent addresses (t1.../t3...) have a public balance.
        if (!preg_match('/^t[0-9a-zA-Z]{20,}$/', (string) $address)) { return null; }  // shielded/unknown -> unverifiable
        $url = 'https://api.blockchair.com/zcash/dashboards/address/' . rawurlencode($address);
        $j = lv_json($url, 'GET', null, array(), 15);
        if (!is_array($j) || !isset($j['data'][$address]['address'])) { return null; }
        $a    = $j['data'][$address]['address'];
        $bal  = lv_norm_int(isset($a['balance'])  ? $a['balance']  : 0);
        $recv = lv_norm_int(isset($a['received']) ? $a['received'] : 0);
        $tx   = (int) (isset($a['transaction_count']) ? $a['transaction_count'] : 0);
        $active = lv_units_pos($bal) || lv_units_pos($recv) || $tx > 0;
        return array(
            'status' => $active ? 'active' : 'inactive',
            'bal'    => lv_units_to_dec($bal, 8),
            'recv'   => lv_units_to_dec($recv, 8),
            'tx'     => (string) $tx,
        );
    }
}

/* ================================================================ DISPATCH === */
if (!function_exists('luck_verify_activity')) {
    function luck_verify_activity($chain, $address) {
        $chain   = strtolower(trim((string) $chain));
        $address = trim((string) $address);
        $UNVERIFIED = array('status' => 'unverified', 'bal' => '', 'recv' => '', 'tx' => '');

        if ($address === '') { return $UNVERIFIED; }

        $evm = lv_evm_rpc();
        $res = null;

        if (isset($evm[$chain])) {
            $res = lv_check_evm_native($evm[$chain], $address);
        } else {
            switch ($chain) {
                case 'usdt':          $res = lv_check_usdt($address); break;
                case 'bitcoin':       $res = lv_check_bitcoin($address); break;
                case 'litecoin':      $res = lv_check_esplora('https://litecoinspace.org', $address, 8); break;
                case 'dogecoin':      $res = lv_check_blockcypher('https://api.blockcypher.com/v1/doge/main', $address, 8); break;
                case 'bitcoin-cash':  $res = lv_check_haskoin('https://api.haskoin.com/bch', $address, 8); break;
                case 'tron':          $res = lv_check_tron($address); break;
                case 'xrp':           $res = lv_check_xrp($address); break;
                case 'solana':        $res = lv_check_solana($address); break;
                case 'sui':           $res = lv_check_sui($address); break;
                case 'ton':           $res = lv_check_ton($address); break;
                case 'zcash':         $res = lv_check_zcash($address); break;
                /* monero: no address-level balance exists on a privacy chain,
                   so it can never be independently verified -> never saved. */
                case 'monero':        $res = null; break;
                default:              $res = null; break;   // unknown chain -> unverifiable
            }
        }

        if (!is_array($res) || !isset($res['status'])) { return $UNVERIFIED; }
        // normalize shape
        return array(
            'status' => $res['status'],
            'bal'    => isset($res['bal'])  ? (string) $res['bal']  : '',
            'recv'   => isset($res['recv']) ? (string) $res['recv'] : '',
            'tx'     => isset($res['tx'])   ? (string) $res['tx']   : '',
        );
    }
}

} /* LUCK_VERIFY_INCLUDED */

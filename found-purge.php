<?php
/* ============================================================================
   found-purge.php  —  one-time / occasional cleanup for the "Found Luck" store.

   Re-verifies EVERY already-stored record against its chain's own public API
   (via luck-verify.php) and rewrites the store keeping ONLY the addresses the
   chain still confirms active — with the chain's real balance/received/tx. This
   is what removes the old fabricated rows that were saved before found.php began
   verifying on-chain.

   CLI ONLY (never reachable over the web). Run it inside whichever directory
   holds the found-data/ you want to clean (each domain keeps its own):

     php found-purge.php               re-verify and rewrite (drops inactive)
     php found-purge.php --dry-run     report only; change nothing
     php found-purge.php --strict      ALSO drop records that can't be verified
                                       (monero / shielded zcash / API down)

   Default keeps "unverified" records (an API outage must not delete a genuine
   hit); confirmed-inactive rows are always removed. A backup of the old file is
   written to found-data/found.jsonl.bak before anything is replaced.
   ============================================================================ */

if (php_sapi_name() !== 'cli') { http_response_code(403); header('Content-Type: text/plain'); exit("found-purge.php is CLI-only\n"); }

error_reporting(E_ALL & ~E_DEPRECATED & ~E_NOTICE);
@set_time_limit(0);

require_once __DIR__ . '/luck-verify.php';

$DIR   = __DIR__ . '/found-data';
$FOUND = $DIR . '/found.jsonl';
$INDEX = $DIR . '/index.txt';
$COUNT = $DIR . '/count.txt';

$dry    = in_array('--dry-run', $argv, true);
$strict = in_array('--strict',  $argv, true);

if (!is_file($FOUND)) { fwrite(STDERR, "No store found at $FOUND — nothing to do.\n"); exit(0); }

/* ---- read every record --------------------------------------------------- */
$records = array();
$fp = fopen($FOUND, 'r');
if (!$fp) { fwrite(STDERR, "Cannot open $FOUND\n"); exit(1); }
flock($fp, LOCK_SH);
while (($line = fgets($fp)) !== false) {
    $line = trim($line);
    if ($line === '') { continue; }
    $r = json_decode($line, true);
    if (is_array($r) && isset($r['address'])) { $records[] = $r; }
}
flock($fp, LOCK_UN);
fclose($fp);

$total = count($records);
fwrite(STDOUT, "Loaded $total record(s) from $FOUND\n");
fwrite(STDOUT, $dry ? "DRY RUN — nothing will be written.\n\n" : ($strict ? "STRICT — unverifiable rows will also be dropped.\n\n" : "\n"));

/* ---- re-verify each on-chain --------------------------------------------- */
$keep = array();
$removed = 0; $kept = 0; $unver = 0; $updated = 0;

foreach ($records as $n => $r) {
    $chain = isset($r['chain'])   ? (string) $r['chain']   : '';
    $addr  = isset($r['address']) ? (string) $r['address'] : '';
    $chk = luck_verify_activity($chain, $addr);
    $status = (is_array($chk) && isset($chk['status'])) ? $chk['status'] : 'unverified';

    $tag = str_pad(($n + 1) . '/' . $total, 9);
    if ($status === 'active') {
        // refresh stored numbers with the chain's verified figures
        $before = array($r['bal'] ?? '', $r['recv'] ?? '', $r['tx'] ?? '');
        $r['bal']  = (string) $chk['bal'];
        $r['recv'] = (string) $chk['recv'];
        $r['tx']   = (string) $chk['tx'];
        if ($before !== array($r['bal'], $r['recv'], $r['tx'])) { $updated++; }
        $keep[] = $r;
        $kept++;
        fwrite(STDOUT, "$tag KEEP    [$chain] $addr  bal={$r['bal']} recv={$r['recv']} tx={$r['tx']}\n");
    } elseif ($status === 'inactive') {
        $removed++;
        fwrite(STDOUT, "$tag REMOVE  [$chain] $addr  (chain confirms empty)\n");
    } else { // unverified
        if ($strict) {
            $removed++;
            fwrite(STDOUT, "$tag REMOVE  [$chain] $addr  (unverifiable, --strict)\n");
        } else {
            $keep[] = $r;
            $unver++;
            fwrite(STDOUT, "$tag KEEP?   [$chain] $addr  (could not verify — kept; use --strict to drop)\n");
        }
    }
    usleep(150000);   // be gentle on the public APIs
}

fwrite(STDOUT, "\nSummary: kept $kept active" . ($unver ? " + $unver unverified" : "") .
               ", removed $removed" . ($updated ? ", refreshed $updated figure(s)" : "") . ".\n");

if ($dry) { fwrite(STDOUT, "DRY RUN complete — store left unchanged.\n"); exit(0); }
if ($removed === 0 && $updated === 0) { fwrite(STDOUT, "Nothing to change.\n"); exit(0); }

/* ---- rewrite the store atomically (lock the index like the writers do) --- */
$fi = fopen($INDEX, 'c+');
if (!$fi) { fwrite(STDERR, "Cannot lock $INDEX\n"); exit(1); }
flock($fi, LOCK_EX);

@copy($FOUND, $FOUND . '.bak');   // safety backup of the pre-purge file

$okAll = true;
$newKept = count($keep);

// found.jsonl
$body = '';
$idxBody = '';
foreach ($keep as $r) {
    $body    .= json_encode($r) . "\n";
    $idxBody .= md5(($r['chain'] ?? '') . '|' . ($r['address'] ?? '')) . "\n";
}
if (file_put_contents($FOUND . '.tmp', $body) === false || !@rename($FOUND . '.tmp', $FOUND)) { $okAll = false; }

// index.txt (rebuild from kept records)
ftruncate($fi, 0); rewind($fi);
if (fwrite($fi, $idxBody) === false) { $okAll = false; }
fflush($fi);

// count.txt
$fc = fopen($COUNT, 'c+');
if ($fc) {
    flock($fc, LOCK_EX);
    ftruncate($fc, 0); rewind($fc);
    fwrite($fc, (string) $newKept); fflush($fc);
    flock($fc, LOCK_UN); fclose($fc);
}

flock($fi, LOCK_UN);
fclose($fi);

if ($okAll) {
    fwrite(STDOUT, "Store rewritten: $newKept record(s) remain. Backup: found-data/found.jsonl.bak\n");
    exit(0);
}
fwrite(STDERR, "WARNING: rewrite hit an error — check found-data/ (backup is at found.jsonl.bak)\n");
exit(1);

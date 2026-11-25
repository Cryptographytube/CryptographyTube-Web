# vulnscan — Bitcoin ECDSA Transaction Vulnerability Scanner

**One** standalone Python file. Give it a Bitcoin address; it fetches the
address's on-chain transactions, rebuilds every ECDSA `(R, S, Z)` signature the
address made, and runs **every transaction/signature-based vulnerability check
that can mathematically recover the private key**. When a key is crackable it
recovers it.

For **every** scanned address that produced signatures it creates a folder named
after the address under `results/` and saves the full `(r, s, z, pub)` dump
**first**, so the heavy attacks can always be re-run offline later. When a
vulnerability is found it also writes **one `.txt` per finding** with the full
detail: what was detected, every value (pubkey, R, S, Z, nonce), the
step-by-step calculation, and the recovered private key (hex + WIF + every
derived address, with a check that it matches the scanned address). Pass
`--no-rsz` to skip the dump.

## One file, no dependencies

Everything lives in `vulnscan.py` — secp256k1 math, the on-chain fetcher, the
tx parser, the RSZ extractor, all the vulnerability checks, the lattice solver,
the report writer, the CLI, and the self-test. Pure Python 3 standard library
only (no pip installs): `urllib` for HTTP, `hashlib` for SHA-256 / RIPEMD-160,
hand-rolled elliptic-curve arithmetic for everything else.

## Data sources

Per project policy this tool **never uses mempool.space**. It fetches from:

1. `blockstream.info` (Esplora) — primary
2. `blockchain.info` — fallback

## Usage

```bash
# scan one address (default: newest 100 transactions)
python vulnscan.py 1BFhrfTTZP3Nw4BNy4eX4KFLsn9ZeijcMm

# scan several — signatures are POOLED so a nonce shared BETWEEN these
# addresses (cross-wallet / cross-chain) is caught and cracks every key
python vulnscan.py 1Addr... 3Addr... bc1q...

# scan more/less history
python vulnscan.py 1Addr... --limit 300

# scan a list from a file (one address per line, # = comment; types may be mixed)
python vulnscan.py --file addresses.txt

# a mixed file, but scan only ONE address type — pick with -all / -1 / -3 / -bc1q
python vulnscan.py -1    --file addresses.txt   # only legacy P2PKH (1…)
python vulnscan.py -3    --file addresses.txt   # only P2SH (3…)
python vulnscan.py -bc1q --file addresses.txt   # only native segwit (bc1q…)
python vulnscan.py -all  --file addresses.txt   # every type (this is the default)

# By DEFAULT a quiet QUICK lattice bit-leak DETECTOR runs on every address, so
# each one gets a real verdict written to its own results/<addr>/_BITLEAK.txt:
#   BIT-LEAK FOUND (model, how many bits, MSB or LSB, which tx, k values, key)
#   NO BIT-LEAK (proven)  — a key was recovered and its nonces are full-size
#   NO BIT-LEAK DETECTED  — the quick sweep found no bias at this dimension
#   UNDETERMINED          — fewer than 4 signatures (a lattice needs several)
#   NOT TESTED            — only with --fast / --no-lattice
# BSGS stays OFF unless --bsgs. The instant-recovery checks always run.

# turn the quick sweep into a DEEP exhaustive RECOVERY — all signatures up to
# --lattice-rows, and (with --bsgs) the small-key search. This is what actually
# CRACKS a bias-only address (biased nonces, no reuse):
python vulnscan.py 1Addr... --lattice --bsgs --bsgs-bits 40 --lattice-rows 60

# the rsz dump is saved for EVERY address, so you can defer the deep attack:
python vulnscan.py <addr> --offline results/<addr>/<addr>_rsz.txt --lattice --bsgs
# --fast / --no-lattice turn the lattice OFF (verdict becomes "not tested");
# --no-bsgs is already the default; --no-rsz skips the signature dump

# offline: no network, feed your own signatures (r:s:z or r:s:z:pubkey per line)
python vulnscan.py 1Addr... --offline sigs.txt

# verify the engine (crafts a real instance of each vuln, no network)
python vulnscan.py --selftest
```

## Supported address types

Full support for all three common single-key script types — the signature is
extracted and the correct sighash `Z` is rebuilt for each:

| Prefix | Type | Sighash | Signature location |
|---|---|---|---|
| `1...` | P2PKH (legacy) | legacy `SIGHASH_ALL` | DER sig + pubkey in `scriptSig` |
| `bc1q...` | P2WPKH (native segwit) | BIP-143 | sig + pubkey in the witness |
| `3...` | P2SH-P2WPKH (wrapped segwit) | BIP-143 | witness sig, redeemScript in `scriptSig` |

The two segwit forms need the prevout amount (BIP-143 binds it into the
preimage), so for witness transactions the scanner fetches each input's spent
value from the explorer automatically. A recovered key is checked against **all
three** address forms it derives, so it matches whichever type you scanned.

> Not covered: P2WSH / multisig, P2TR (Taproot / Schnorr — a different scheme),
> and bare/non-standard scripts. Those don't expose a single-key ECDSA `(R,S,Z)`
> the recovery math can use.

## What it checks

### Recovers the private key (transaction math)

| Vulnerability | Needs | How |
|---|---|---|
| **Nonce reuse (RSZ / RFC6979 collision)** | 2 sigs, same `R` | `k=(z1−z2)/(s1−s2)`, `x=(s1·k−z1)/r` |
| **Negated-nonce reuse** | 2 sigs, same `R`, one signed `−k` | `k=(z1−z2)/(s1+s2)` (R and −R share `x`) |
| **Shared nonce across keys / chains** | same `R` under ≥2 keys + one same-key collision to pin `k` | pin `k` from the same-key reuse (verified `x(k·G) mod n == r`), then cascade `d=(s·k−z)/r` to **every** key that signed under that `R` — one shared nonce cracks them all |
| **Polynonce** | 2 consecutive sigs | `k2 = k1²+c` → solve quadratic mod n |
| **Arithmetic-progression nonce** | 3 sigs + pubkey | `k_{i+1}=k_i+δ` (δ unknown) → `k1−2k2+k3=0` linear in `x` |
| **Geometric-progression nonce** | 3 sigs + pubkey | `k_{i+1}=q·k_i` (q unknown) → `k2²=k1·k3` quadratic in `x` |
| **Affine / LCG nonce** | 4 sigs + pubkey | `k_{i+1}=A·k_i+B` (A,B unknown) → `(k3−k2)²=(k2−k1)(k4−k3)` quadratic in `x` |
| **Pairwise nonce relations** | 2 sigs + pubkey | consecutive `k2=k1+1`, additive `k2=k1+c`, negated `k2=−k1`, proportional `k2=m·k1`, small-difference → generic solver `x=(α·a1+β−a2)/(b2−α·b1)` |
| **Guessable single-sig nonce** | 1 sig | `k ∈ {1..4096, −1..−4096, 2^i, z, r, s, z±r}` → `x=(s·k−z)/r` |
| **Nonce = private key** | 1 sig, `R==pubkey` | `x = z/(s−r)` |
| **Lattice / HNP** (bit-leak) | ≥4 sigs, biased nonces (no `r`/`s` repeat needed) | minerva (MSB-zero) / truncated (short) / lsb (LSB-zero, ladder 8/16) → integer LLL + `solveHNP`; a genuine-bias gate rejects any key whose nonces aren't actually within the model bound. **Runs a QUICK sweep by default** (dim ≤ 40, quiet) to give every address a verdict; `--lattice` = deep exhaustive recovery |
| **Small key** (`--bsgs` only) | just the pubkey | baby-step giant-step over `[1, 2^B)`; cost ≈ 2^(B/2), ceiling ~2⁴⁸–2⁵⁰. **Off by default — runs only with `--bsgs`** |
| **Bit-leak verdict** | every address | a per-address `_BITLEAK.txt` states whether a nonce bit-leak exists — FOUND (model / bits / MSB-or-LSB / which tx / `k` values / key), NO (proven, from a recovered key), NO (quick sweep clean), UNDETERMINED (<4 sigs), or NOT TESTED (`--fast`) |
| **Weak / low nonce** | after any recovery | flags nonces with far fewer than 256 bits |

### Detection only (flagged, no key)

| Flag | Meaning |
|---|---|
| **Invalid signature** | `r` or `s` is `0` or `≥ n` — malformed/forgeable |
| **Zero message hash** | `z = 0` — degenerate signature |
| **Message = r** | `z = r` — suspicious relation |
| **Duplicate broadcast** | byte-identical `(R,S,Z)` — not solvable, but reported |

The recovery math mirrors `assets/js/attack-worker.js` (RSZ, polynonce, the de
Weger integer LLL + HNP `solveHNP`, and the minerva/truncated/lsb/yubikey
lattice models); the signature-extraction pipeline mirrors the
`txid-rsz-recovery` engine — so recovered keys and the `z` (sighash) values
match the website exactly.

### A note on the lattice / bit-leak attacks

**A nonce is secret.** You can only learn a nonce's bits — and therefore *detect*
a bias — in one of three ways: (1) the same `r` repeats (reuse hands you `k`
directly), (2) the private key is already recovered by some other check (then
`k = (z + r·d)/s` for every signature), or (3) you run the lattice, which
recovers the key *by assuming* a bias and so acts as the detector. There is no
way to see an MSB/LSB bias in nonces that never repeat without either a repeat or
the lattice.

So the tool splits this cleanly:

- **By default (no flags), a quiet QUICK lattice bit-leak detector runs on every
  address** and writes a `_BITLEAK.txt` verdict for each one — because running the
  lattice is the *only* way to get a yes/no on a nonce that never repeats. It
  sweeps all three models (minerva MSB-zero, truncated short-nonce, lsb LSB-zero)
  at a modest dimension (≤ 40), silently. The per-address verdict is one of:
  **BIT-LEAK FOUND** (with model, how many bits, MSB or LSB, which transaction,
  the `k` values, and the recovered key), **NO BIT-LEAK (proven)** — a key was
  recovered by another check and its real nonces are full-size, **NO BIT-LEAK
  DETECTED** — the quick sweep found no bias at this dimension (it lists which
  models it could test and which it skipped for too few signatures), or
  **UNDETERMINED** — fewer than 4 signatures, so no lattice model can run. A
  genuine-bias gate means a key whose nonces are *not* actually bounded is never
  mislabeled a bit-leak. Every instant-recovery check still runs alongside this.

- **`--lattice` / `--bsgs` turn the quick sweep into a deep RECOVERY.** This runs
  the integer LLL over **all** signatures (up to `--lattice-rows`, default 120) at
  a raised dimension, and the BSGS small-key search (to `2^--bsgs-bits`). This is
  what cracks a **bias-only** address that the quick pass only *suspected* or
  couldn't reach — the weak-bias models (LSB, small MSB bias) only succeed with
  *many* signatures (an 8-bit bias realistically needs 60–100+, not ~40). BSGS
  cost is ≈ 2^(B/2) in time *and* memory, so its realistic ceiling is ~2⁴⁸–2⁵⁰
  (clamped at 2⁵⁰) — it can **not** search the full 2²⁵⁶ keyspace. `--lattice-rows
  N` caps the lattice dimension. `--fast` / `--no-lattice` turn the lattice off
  entirely (the verdict then reads "not tested").

Because the `(r, s, z)` dump is saved for **every** address first, the usual
workflow is: run the fast default pass over a big list, then re-run only the
addresses you care about with `--offline <addr>_rsz.txt --lattice --bsgs` to test
them for a bias-only bit-leak. `--fast` (or `--no-lattice` / `--no-bsgs`) just
makes the already-off state explicit.

### Live counts & the resume/progress file

A multi-address run (`--file`, or several addresses) prints a running count after
each address — `checked X/Y address(es); vuln found in Z so far` — and a matching
total at the end. The resume state file (`results/.progress_<hash>.txt`) records,
next to each finished address, **which** vuln(s) were found: nothing for a clean
address, the vuln name(s) (comma-separated) when one or more were found. A
restart after Ctrl-C / crash / shutdown skips the addresses already listed there.

## Output layout

```
vulnscan/
  vulnscan.py            <- the entire tool
  README.md
  results/
    1BFhrfTTZP3Nw4BNy4eX4KFLsn9ZeijcMm/
      1BFhrfTTZP3Nw4BNy4eX4KFLsn9ZeijcMm_rsz.txt   <- ALL sigs (r:s:z:pub), offline-ready
      _BITLEAK.txt                                 <- ALWAYS written: the bit-leak verdict
      _SUMMARY.txt
      rsz_nonce_reuse_0_1.txt
      polynonce_3_4.txt
      guessable_nonce_5.txt
      nonce_equals_privkey_2.txt
      pairwise_nonce_relation_6_7.txt
      bitleak_0-4_n5.txt
      lattice_hnp_0-39_n40.txt
      weak_nonce_5.txt
```

`_BITLEAK.txt` and the `*_rsz.txt` dump are written for **every** scanned address
that produced signatures — even one with no vulnerability (the rsz dump unless
`--no-rsz`). `_BITLEAK.txt` is the plain-language bit-leak verdict for that
address; the rsz dump holds every reconstructed `(r, s, z, pub)` in the exact
`--offline` format, so even if a scan is interrupted the signatures are saved and
you can re-run the heavy attacks on them later with no network:

```bash
python vulnscan.py <addr> --offline results/<addr>/<addr>_rsz.txt --lattice --bsgs
```

### Rate-limits: it waits, it doesn't quit

If an explorer rate-limits or errors, the scanner tries the fallback explorer,
and if both are unavailable it **pauses in place** — backing off and retrying —
until the limit clears, then resumes from the exact transaction it stopped on.
No progress is lost and nothing is skipped. Press Ctrl-C to abort a wait.

Each `.txt` contains the address, balance, the involved transactions, all raw
values, the full derivation, and — when cracked — the private key in hex + WIF
plus every address form it produces (with a check that it matches the scanned
address).

## Deliberately NOT included (and why)

Only vulnerabilities that recover a Bitcoin private key from an address's own
on-chain **ECDSA** signatures are implemented. These are out of scope:

- **Brainwallet / passphrase attacks** — removed on purpose: the weakness is in
  a guessed passphrase, not inside the transaction/signature.
- **Schnorr / Taproot (BIP-340)** — a *different* signature scheme. This tool
  reconstructs legacy / segwit-v0 **ECDSA** `(R,S,Z)` tuples only.
- **Ed25519 nonce attacks** — a different curve (not secp256k1); belongs to
  Solana / TON / XRP, not Bitcoin.
- **Other chains** (Ethereum / Litecoin / Bitcoin Cash / Dogecoin / Zcash
  nonce reuse) — the math is identical, but this tool fetches **Bitcoin** data.
- **Cross-curve nonce reuse** (e.g. a secp256k1 key reused on Ed25519) — a
  different curve; the secp256k1 cross-**key** / cross-**chain** case (same curve,
  different addresses) *is* covered by the pooled shared-nonce sweep.
- **Partially-known-nonce / partially-known-key / known-middle-bits /
  one-bit-leak / two-signature-half-nonce** — need extra side-channel bits that
  an address alone doesn't provide.
- **Cubic / higher-degree sequence nonces** (`k2=k1³+c` and up) — the practical
  arithmetic (AP), geometric, affine/LCG and quadratic (polynonce) sequence
  models above already cover the recoverable two-to-four-signature cases.
- **Dark Skippy, timestamp-nonce, RFC6979 public-entropy** — need malicious
  signer artifacts or external entropy hints, not passive on-chain data.

## Legal / ethical

For security auditing and education — to demonstrate that an address's own
signing history has leaked its private key on-chain. Only scan addresses you
own or are authorized to analyze.

# Z6 — original-terminal row invariance under eligible noise

Base `0a9ffe45a` (`origin/v8-reference`); branch `codex/z6-digit…`: see
`evidence-Z6.json`. Exact M31/QM31 computation on the Z4 probe's real traces;
not a Lean proof. Written by the lead from the computation worker's report
(the worker's environment could not write this file); the JSON, logs and
sources in this directory are the worker's.

**Verdict.** Over all 1,000 (witness, tape, challenge-prefix) combinations
(10 witnesses × 5 eligible-noise tapes × 20 challenge vectors), the original
terminal evaluated at every one of the 1,024 Boolean rows is **identical with
and without the noise** — row-level invariance, not only of the total. Every
hypercube total (with noise, without, and the difference) is `[0,0,0,0]`. No
counterexample.

**Why (two facts).**
1. **H1 is untouched.** The helper reads only copy-endpoint cells: all 2,160
   cell reads (136 links, 272 tuples) are on copy-active rows, at non-eligible
   cells, and never on row 1023. (Lean: `HelperInvariant.helper_eligible`.)
2. **No terminal lane reads a noised cell.** No terminal value at any Boolean
   row depends on any of the 3,803 eligible cells or the 16 cells of row
   1023. Tested by perturbing each cell at its three reader rows
   {r, r−1, r⊕12} with two random deltas, on the honest base and two uniform
   random bases; with terminal degree ≤ 25 a missed dependence has probability
   ≈ 25/2³¹ per test.

**Structural rule, derived from source for the largest family.** The terminal
at a Boolean row b reads the trace only through `rowOpenings t b` =
(b, succRow b, xor12Row b) (`R0P/Core.lean:41–45`) in
`eqValue·Σθⁱ·laneAt(o, h1, selAt) + μ·h1 + μ²(1−activeAt)·h1`
(`R0P/SemDecision.lean:74–80`). `eligible` (`R0Z/MaskLayout.lean:38–42`)
lists 3,803 cells: 2,736 Poseidon padding cells (local rows 13–15 of each
16-row block below 912), 936 in rows 912–1007 and 131 in rows 1008–1023; it
matches the Rust inventory `pair_forest_hiding.rs:233–252` cell by cell.
Poseidon padding: branch weights are `local[0]`, `local[1,9,10]`, `local[2..8]`,
and xor12 enters only through `leading_pair` weighted by `local[0]`
(`state_only_poseidon.rs:589–593`); a padding cell at local row 13–15 is read
as z by local rows 13–15, as succ by 12–14, as xor12 by 1–3; none of those
rows is in {0..10} and at rows 1–3 the xor12 weight `local[0]` is 0, so every
coefficient is identically zero. The other families (schedule, occupancy,
path, value, digest, asset, copy selectors on rows 912–1023) were NOT audited
from source; the randomized test found zero dependence for all of them.

**Also observed.**
- `balance` rewrites row 1023 in all 16 semantic columns and nothing else;
  no Boolean row's terminal reads those cells, so the balanced zero-noise
  trace (A) equals the raw trace (C) at every row (200/200).
- The helper is 0 on all 810 inactive rows, so the Lean honest view's (A)
  equals Z4c's balanced trace (200/200).
- (A) is not the zero vector: it is nonzero on the 194 copy-active rows
  (trial 0, witness 0), where it equals μ·h1(b); its total is 0.
- The H1-padding block of the affine tape changes exactly the 810 inactive
  rows, by (μ+μ²)·pad(b), with total change 0 (balance).
- 221 eligible cells lie on copy-active rows (columns 9–15 of the path base
  rows 913, 917, …, 1005; cells on rows 1008, 1010, 1012, 1014, 1015, 1017,
  1018). `balance` sums only `copyInactiveRows`, so these are not compensated
  at row 1023; they are read by neither the helper nor any terminal lane.
  The first preflight asserted no such cells exist and failed; retained.

**Runs** (build host, own scopes, MemoryHigh 3G / MemoryMax 4G / swap 0,
release profile, rustc 1.94.1): preflight1 compile 47.5 s / 546,380 KiB;
preflight1 probe exit 101 (the wrong assertion above); preflight2 compile
5.3 s; preflight2 probe 4.8 s; full compile 5.4 s; full probe 21.6 s,
peak child RSS 18,304 KiB, cgroup peak 199,745,536 B; swap 0 throughout;
no cap raised. 204 compiled-source hashes verified. All 20 challenge records
byte-identical to `probe-C.log`. Artifacts: `z6.rs`, `probe.rs` (`--z6`
dispatch only), `run-z6.py`, `summarize-z6.py`, `probe-Z6.log`,
`summary-Z6.json`, `evidence-Z6.json`, `z6-runs/`. Host copy
`/home/dombarker/project-offloads/aspis-z6-20261011/`. No Lean run; no
production Rust changed; no binaries; no trailer.

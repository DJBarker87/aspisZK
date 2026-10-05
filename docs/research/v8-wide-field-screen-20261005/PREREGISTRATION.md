# Wide-field cost screen: criteria fixed before measurement

2026-10-05. Branch `research/v8-wide-field-screen-20261005`, from the audit
commit `8bf5aa1e0`. Research only. No verifier, prover, protocol or parameter
of any profile is changed; nothing under `crates/` or `programs/` is edited.

This file is committed before the probe is built or run. The results file
must apply the rules below as written.

## Question

Two candidates were proposed to replace the degree-4 challenge field of the
R102 profile: degree 6 and degree 8 over M31, each with 32 queries instead of
22. Can either fit the compute cap on the measured R117 engine?

Reference point: the R117 endpoint, 999,790 CU on the larger fixture under
the 1,000,000-CU cap (210 CU of margin). The Solana per-transaction maximum
is 1,400,000 CU.

## Fields

- K4 = QM31 as in `aspis-core` (`u^2 = 2 + i`).
- K8 = QM31[v]/(v^2 - u). `fields.py` checks that `u` is a non-square in QM31.
- K6 = CM31[w]/(w^3 - (2 + i)). `fields.py` checks that `2 + i` is a non-cube
  in CM31.

Neither construction has a Lean proof. The Python check is the evidence.

## Measurements

One standalone SBF program, LiteSVM, the prebuilt driver used for R101–R117
(`--micro`, 256 KiB heap, diagnostic cap). Each number is taken five times
and must be identical. Every kernel output is compared in-program with a
value computed by `fields.py`; a mismatch is a failed run, not a data point.

M1, per-operation cost. Chained operations `x <- x * y`; cost per operation
is `(CU(2000 ops) - CU(1000 ops)) / 1000`.

- field multiplication in K4 (the `aspis-core` `QM31::mul`), K6, K8;
- multiplication of a field element by an M31 scalar in K4, K6, K8;
- inversion in K4 and K8 (`(CU(200) - CU(100)) / 100`). K6 inversion is not
  measured.

M2, authentication with leaf hashing. Two eight-way trees of depth six over
262,144 synthetic public leaves, 26-byte digests, parent domain `0x18`, one
SHA-256 call per opened leaf input and per parent. C1 leaf input 437 bytes.
C2 leaf input 220 bytes at degree 4, 313 at degree 6, 406 at degree 8 (12
field values, 31 bits per coordinate, plus the 34 bytes of tag and salt).
Configurations: (22 queries, 220), (32, 313), (32, 406), and (32, 220) to
separate the query effect from the width effect. Two index sets each.
`A(q, w)` is the whole-program CU, larger of the two index sets.

M2 is authentication only. It is not an Aspis proof execution.

## Rules

Kernel prediction. `r8 = mul(K8)/mul(K4)` and `r6 = mul(K6)/mul(K4)`.
Predicted from operation counts: `r8` about 3, `r6` about 2. The kernel is
"as predicted" if `r8 <= 3.5` and `r6 <= 2.6`; otherwise it is reported as
worse than predicted. This is reported, not a pass/fail by itself.

Floor. For candidate degree `d` with 32 queries,
`F(d) = 999,790 + A(32, w_d) - A(22, 220)`. The floor charges only the extra
hashing and assumes every field operation costs the same as today.

- `F(d) > 1,400,000`: HARD FAIL. The candidate cannot fit one transaction.
- `1,000,000 < F(d) <= 1,400,000`: FAIL AT THE 1M CAP on the engine as it
  stands. The candidate needs new savings of at least `F(d) - 1,000,000`,
  plus all growth in field arithmetic.
- `F(d) <= 1,000,000`: possible only if the extra hashing costs at most 210
  CU.

Ceiling (arithmetic-scaled, not measured).
`C(d) = F(d) + (r_d - 1) * (999,790 - A(22, 220))`: every CU of the current
verifier outside authentication is treated as challenge-field multiplication.

- `C(d) <= 1,400,000`: the candidate fits the Solana maximum whatever the
  arithmetic share.
- otherwise the screen is UNDETERMINED AGAINST 1.4M between `F(d)` and
  `C(d)`. Resolving it needs a multiplication census of the R117 engine,
  which is not in the tree.

## Expected outcome, stated in advance

The margin is 210 CU and ten more queries cost thousands of CU of hashing, so
"FAIL AT THE 1M CAP" is expected for both candidates. The screen is run for
the numbers: `r6`, `r8`, the hashing increment, and how far the floor sits
above the cap.

## Not covered

Packed decoding of wider C2 records; opening, fold and relation arithmetic in
a wide field; a second final array; proof size (reported by arithmetic only);
soundness of any candidate; privacy of any candidate. The K4 control is the
generic `aspis-core` multiplication, not the specialised kernels of the R117
engine; the ratios assume a wide kernel built the same way from whichever K4
kernel is used.

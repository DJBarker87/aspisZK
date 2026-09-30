# R106–R117: complete acceptance at the actual 1M cap

Base `5dbb33eb8ccca9db8f4d882826e67ef3e1922954`, 2026-09-30.
Branch `research/v8-r64-guarded-m31-20260929`.

**The two genuine proofs now complete at 999,790 / 999,532 CU under the
actual 1,000,000-CU cap. Full privacy and soundness remain unproved.**
The larger run has only **210 CU of margin**. This is a measured two-fixture,
verifier-only milestone, not a universal execution bound or production release.
The next priority is the source-grounded security proof, with broader resource
coverage still required before relying on this thin margin operationally.

## Complete executions, not summed estimates

| Exact-output candidate | World 0 CU | World 1 CU | Decision |
|---|---:|---:|---|
| Pushed R105 control | 1,066,127 | 1,065,886 | Retained control |
| R106 private terminal and inactive-sum program | 1,048,938 | 1,048,652 | Compose |
| R107 semantic evaluation/basis fusion | 1,064,587 | 1,064,343 | Compose |
| R108 aligned dynamic packed reader | 1,159,096 | 1,158,855 | Reject |
| R109 private chord geometry | 1,061,752 | 1,061,519 | Compose |
| R110 private base/complex norm batch | 1,062,805 | 1,062,563 | Included by R112 |
| R111 fixed-offset packed reader | 1,072,587 | 1,072,346 | Reject |
| R112 private final complex product, on R110 | 1,055,631 | 1,055,385 | Compose |
| R113 cross-coordinate Copy sums | 1,054,504 | 1,054,263 | Compose |
| R114 fixed Copy-tag program | 1,061,769 | 1,061,528 | Compose |
| R115 measured composition | 1,016,546 | 1,016,260 | Retain |
| R116 query injection and tail, on R115 | 1,003,633 | 1,003,365 | Retain |
| R117 private final-vector fold, on R116 | **999,790** | **999,532** | Selected native endpoint |

Except where noted, isolated candidates start from R105. R115 composes R106,
R107, R109, R112 (including R110), R113 and R114. The two packed-reader
regressions are excluded. Their correctness gates and measured losses remain.
No isolated savings are added to manufacture the composition result.

Every completed candidate accepts both honest proofs at the diagnostic cap.
Only R117 accepts both at the actual 1M cap; earlier cap exhaustion is not a
security rejection. Corrupted combined finals reject with **Custom(6)** at
both caps, including R117 at 786,270 / 787,465 CU. Heap is unchanged at
262,144 bytes and simulated accounts are unchanged. No network transaction,
settlement, deployment, wallet operation or merge was performed.

All candidates reuse R102's exact 57,682-byte proofs:

```text
world0 f135026ea47db2b9404814c0e076b0bf743974c8b2d646628060b661be943877
world1 2ac3c200bca21acffe4864d3a81e5d003da89e306d05d2bc5c6c0a979f47afc1
```

Selected source manifest:
`26755a4250ec6075005e840565040414b694deb97fb1830fc95aff2692d34fb6`.
The effective profile remains
`AV8/R102/sparseG-bitperm-two-swaps/quadratic-channel-fold/merkle8-research-v1`.
No field, challenge, digest, query-count, leaf, commitment or wire parameter
changes in this campaign. Both commitments, all canonical/domain/authentication
checks, image residuals and final relation checks remain.

## What changed and what was checked

R106 keeps the shared high/final adjoint, ordinary correction and sparse-G
contraction in the existing private canonical representation. A source-pinned
integer common-subexpression program reduces inactive-mask additions from
210 to 77 (normal) and 97 to 64 (carry). It preserves the two swaps, pivot,
carry zero extension and exact inactive inventory. The raw fallback remains;
zero beta does not skip validating any G coin. Checks: 512 complete profiles,
65,536 geometry coordinates, 12,160 inactive coordinates, 3,252 malformed
controls, and every basis direction of the generated integer map.

R107 shares the same semantic basis and evaluation inside one private region.
It retains basis order, claim recurrence, raw fallback and the independent
Horner oracle. Checks: 8,192 rounds, 221,184 basis coordinates and 1,044 raw
boundary cases. Its small complete saving is not described as a large win.

R109 uses canonical chord/basis geometry and exact nested halvings for the
existing carry walk. Checks: 8,192 profiles, 286,720 coordinates, 84 malformed
boundary cases, plus the retained actual two-swap dense functional oracle.

R110 preserves the coefficient equations, shared batch inversion, shape and
zero checks while carrying private M31/CM31 values through the norm batch.
R112 retains folded weights privately through the final QM31-by-CM31 product.
Checks include 393,216 base/complex arithmetic comparisons, 512 inversion
batches, all 132 zero positions, 69,632 final complex products, and the R99
gate's 174,288 weights and 87,144 complete folds. Canonical-product reduction
is not substituted for the general unrestricted-u64 reducer.

R113 is **not** the failed within-row deduplication from R105. It shares sums
across 73 Copy outputs: 152 unique inputs, 59 common sums, reducing the
per-limb addition schedule from 471 to 164. Expansion is checked exactly over
the integers, and a Rust constant gate binds every one of the original 544
ordered terms. Positive intermediates have at most 272 arbitrary-u32 terms
and are below 2^41. Checks: 2,048 raw-u32 gathers plus the retained 70,720
selector-predicate checks and 512 full-lane comparisons, both variants.

R114 compiles the fixed tag matrix, retaining all 272 source endpoints,
R58's base shift, append/variant behavior and all pattern weights. Its
positive intermediates are below 2^48 even for arbitrary-u32 source limbs.
Checks: 30,720 raw-coordinate comparisons and the retained 9,600 tag
coordinates, 640 complete finishes and 2,978 omitted-base negatives.
The additional 480-byte internal buffer is included in the unchanged-heap
complete measurements, not excluded from the budget.

R108 and R111 preserve the 31-bit packed bytes and every canonicality check,
including all eight alignments. R111's exact bit-origin generator and host
basis test cover 37,696 cases; each reader has 32,768 accepted comparisons
and 1,807 malformed cases. Both regress on complete SBF and are rejected.

R116 specializes the actual single line-query component. Injection retains
rho^1 through rho^22 and the identical absorbed increment. No query weight
is read by intervening transcript operations, so deterministic weight folds
are evaluated together after the same three challenges have been sampled.
The final four coordinates use bounded limb sums and one final reduction,
not 22 independent generic tensor-prefix allocations. No challenges, fields,
message ordering or sampled-query observations move. Invalid raw boundaries
retain a reference fallback; incoming proof parsing remains mandatory.
Checks: 2,048 profiles, 8,192 intermediate prefix comparisons, 64 independent
dense fold comparisons, maximal-limb accumulator boundaries, 642 malformed
controls and empty/mismatched shape rejection.

R117 retains canonical challenge powers across each owned Final256 fold.
The same affine short-dot formula now receives private operands, avoiding
repeated challenge validation and prepared-value reconstruction. Every
input block is still validated; raw blocks use the retained implementation.
Checks: 4,096 profiles, 44,032 folded coordinates, 1,536 tail-stage comparisons,
216 raw boundary cases, partial-chunk behavior and independent Horner results.

For each new assembled source: focused optimized host gates, both existing
proof audits, **3,282 full-wire cases** (one acceptance and 3,281 checked
rejections), SBF stack/table gates and all eight complete runtime cases pass
their stated expectations. The recorded public transcript prefixes are equal
across every successful native variant. This does not replace a formal
whole-source refinement proof.

## Evidence and retained failures

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r117_evidence.py
```

Public evidence pins every stage, immediate parent, source delta, focused
test, command, wall time, peak process RSS, swaps, fixture hash, ELF and full
runtime receipt. Private fixture contents, ELF binaries, raw register dumps
and wallet keys are not collected. Frozen source trees remain on the NUC;
the committed tools and content-addressed source deltas preserve the work.

Two ordinary host compile failures are retained: R113-A attempted `println!`
inside a no-std library; the repaired harness prints its returned count.
R115-A's combined host-only R107 harness lacked the corelib alias required by
R112's differential helper. R115-B adds that alias, not a protocol change.
Neither failed build was benchmarked or rerun with a larger memory cap.

The R115 trace is byte-identical to the measured ELF and matches its
1,016,546 CU; it records 942,048 executed instructions. Those are exclusive
instruction counts, not R117 profiling or additive region CU. The first
collector queried transient systemd units after disposal and received default
properties. This is retained as a metadata failure, **not** evidence of the
actual job caps. One trace-only repeat captures caps from its live cgroup;
the original trace remains. No arithmetic/formal suite is repeated for that
metadata repair.

Heavy jobs use the cached Tailscale NUC, optimized Rust, overflow checks,
TasksMax=128 and MemorySwapMax=0. Host caps are 5/7 GiB high/max, SBF 12/16,
runtime/trace 2/3, analysis/collection 1/2. Concurrent caps stay below 26 GiB.
The Solana skill's source-equivalence, malformed-input, stack and complete
execution gates determine selection. **No new Lean target was compiled in
this native campaign**, and no unchanged formal manifest was replayed.

## First remaining security proposition

Prove **universal actual-source C1/H1/G joint affine-image compatibility for
the two-swap sparse-G profile**, retaining p0/p2 and every other disclosed
coordinate, for every legal same-public-witness difference and adaptive or
degenerate prefix; otherwise supply source-justified exceptional-event losses.
The two actual-prefix corrections are not a universal theorem. R49/R50's
old T163 specialization cannot simply be relabeled as the new profile.

Then retain the conditional posterior through the complete causal simulator;
compose actual seed expansion, C2, both eight-way commitments and one shared
oracle; account for observable failures, retries and publication. Soundness
separately needs coherent original quotient-pair extraction **before beta**,
the actual challenge law and all extraction/list/Fiat–Shamir losses. Compiled
word/native-kernel refinement and broader resource coverage remain explicit.
R100's observed-query theorem is reusable but is not whole-experiment
composition. The C1 leak, one-swap H1 rank-539, older rank-517 and bad-schedule
negatives remain. No new hiding assumption or security promotion is claimed.

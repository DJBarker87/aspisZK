# R17 CU review: exact-arithmetic optimization candidates

Review date: 21 September 2026.
Initially inspected `2c03cc7b5dad76d731ae0628eef233b98eb034b1`.
Rechecked branch and reviewed newer HEAD `020ab456a0d50aad0b61317e06b2e024e897f677` (R34–R36).

**This is working source, an independently executed arithmetic checker, generated constants and integration drafts—not another instruction-only packet. No changes were pushed to GitHub.**

## What the latest repository actually measures

R36 primary accepts its new research-v2 fixture at 20,591,164 diagnostic CU.
G original weights cost 12,894,084; dual 94,939; chord 2,258,151: total 15,247,174.
The G original interval contains a 3,927,444-CU numerator tree and a 6,613,168-CU final FFT interval (do not add these again to the original total).
The ordinary compact terminal costs 1,568,856. An additional 870,395 CU lies between opened-authenticated and openings-end, where the retained combined-opening reference is called.
The full program still fails during its second dense reference pass. All supported 1.2M/1.4M cases still exhaust CU.
These are repository-reported SBF observations, NOT measurements made by this pack.

R36 already fixes the edge-vector allocations / consumed-workspace handoff and introduces versioned compact descriptor binding for the ordinary channel. **Do not redo those as new optimizations.** Shared inversion, affine folds, tensor complement expansion and fixed FFT specialization are also already retained. The R25 DIF attempt was an SBF regression: build further experiments from the R24-derived route, as R36 does.

## 1. Highest-value new bounded experiment: cyclic G transform

`MATHEMATICS.md` proves the exact algebraic identity for computing the SAME 271-to-1024 power-sum map with 1024-point rather than 2048-point final transforms.

The existing numerator denominator tree can be reused. Scale each input by the fixed base-field constant `1-a^1024`; divide in the 1024-point Fourier domain by D; replace the single singular DC frequency explicitly. Do not simply shrink the old convolution: that wraps the high tail and is incorrect.

Files:
- `check_optimizations.cpp`: independent complete implementation of old 2048, new 1024 and direct power-sum evaluation; executed successfully.
- `generate_cyclic_tables.py`: independent Python table generator and self-check.
- `r17_cyclic_tables.rs`: generated public constants. Only frequency zero is a sentinel.
- `cyclic_g_apply.rs`: **uncompiled** source-integration draft for the R24-derived helper. It retains the short hybrid numerator merges, caller-owned output scratch, separate CM31 components, and no challenge-dependent control flow.

The final-transform butterfly visit count is 45,056 -> 20,480 across both components, a 54.545% reduction. Pointwise spectrum multiplications go 4,096 -> 2,046. The shared complex workspace can shrink from 16 KiB to 8 KiB. There is extra fixed coin/DC scaling. These are algorithmic counts, NOT an SBF CU percentage.

Integration: add `1024,false/true` to `fft_fixed` dispatch and its controls, using the old ROOTS table at stride two and inverse scaling 2^21. Keep host old-2048 and direct comparators. Use the new constants only for the final transform; retained short-merge denominator spectra remain valid. Do not import the rejected R25 DIF changes. Bind new constant hashes in a fresh staging manifest. Compare the exact same v2 proof bytes and every exposed transcript field under old/new arithmetic.

A source-wide Lean/word proof and compiled Rust/SBF test are NOT provided here. The proof is a paper algebra derivation plus executed independent exact-arithmetic tests.

## 2. Immediate small arithmetic simplification: nested halves

`carry_shortcuts.rs` supplies uncompiled Rust leaves for the owned chord's `xt_at` and the weighted grouping carry calculation. Replace geometric-weight scalar products by backwards nested `add(...).half()`.

The three chord passes visit 513 + 512 + 512 entries. At the explicit source operation level this removes 13,813 M31 multiplications (including scale updates and four limbs per mul_m31), replacing them with 1,533 QM31 halves. The other chord multiplications remain. This is not a measured compiler instruction reduction.

The readers are PURE array accesses. The new order must NOT be used on stateful/random-oracle callbacks. Preserve the 513 intermediate coordinate and the zero extension at grouped index 64. Never prune the 64 output groups merely because the input support is shorter.

The same file supplies the exact `coordinate(1023)` shortcut: it has only local normal slot 15 and high slot 15, no carry. Its terminal is `[0,0,0,normal[15]*high[15]/256]`. Other coordinates remain unchanged. This saves a complete generic group traversal at that call site.

## 3. Separate the diagnostic reference from the actual production path

The current primary `opened` still invokes the old combined-opening verifier after actual packed decoding, domain checks and paired Merkle authentication. The separately invoked full dense verifier is another layer of diagnostics.

Potential production saving: host/CI-only independent reference checks, while retaining ALL actual canonical checks, denominator checks, Merkle authentication, both quotient channels, image residuals and relation acceptance tests. This requires an explicit equivalence/source decision—not silently deleting a failed check or claiming a resource abort is a valid rejection.

The measured 870,395-CU interval is a profiling target, not a guarantee of exactly that saving after changed instrumentation/allocation. Removing the separate SECOND complete verifier does not lower the already-reported primary CU count.

## Benchmark order

1. Run the independent checker and generator here.
2. Integrate nested halves + pivot into a fresh R36 stage; run existing actual-source/dense comparisons, malformed controls, source/frame/allocation gates and SAME-proof SBF measurement.
3. Integrate cyclic final FFT with the old numerator, fast fixed butterflies and same v2 transcript. Re-run every 271 input basis position with all four tower limbs, dirty-output buffer tests, complete weight/fold tests, same proof, malformed cases, and CU/heap measurements.
4. Make a separate, explicit production-vs-diagnostic reference-path decision and benchmark it separately.
5. Continue true compact G preparation/terminal work. Even removing all current G preparation would leave 5,343,990 primary CU on this fixture: local arithmetic improvements alone do not establish a 1.4M verifier.

No mutation of mixing nodes, 271 coordinate placement, image constraints, proof format, commitments or challenge framing is proposed by optimizations 1 and 2. Exact mathematical output preservation is the target; resource-failure behavior may improve and is not claimed pointwise identical.

## Evidence and reproduction

Run `./run_checks.sh` on a machine with Python 3 and g++.
`verification.json` records the accepted C++ output. Tests cover:
- 542 CM31 basis vectors (271 coin positions x two base-field limbs);
- 32 complete QM31 vectors, checked via their two CM31 components against BOTH old and new algorithms and an independent direct sum;
- 1,023 nonsingular fixed Fourier inverses and the unique singular frequency;
- 82,000 carry comparisons, 80 complete grouped contractions and 80 pivot cases;
- negative controls for naive 1024 wrapping and omitted singular-frequency correction.

The independent checker uses exact integer modular arithmetic, no floating point. Its C++ field implementation is not the extracted Rust field implementation. Rust, Lean, SBF and a Solana VM were unavailable here; none was run or claimed. An initial -Werror indentation warning in the C++ harness was corrected before the accepted build. All accepted checks subsequently passed unchanged.

## Source pins / primary evidence

Repository URLs below are pinned, not moving-branch references.

Latest commit:
https://github.com/DJBarker87/aspisZK/commit/020ab456a0d50aad0b61317e06b2e024e897f677

Latest measurements:
https://github.com/DJBarker87/aspisZK/blob/020ab456a0d50aad0b61317e06b2e024e897f677/docs/research/v8-full-view-zk-20260912/R17_COMPACT_PREPARE.md
https://github.com/DJBarker87/aspisZK/blob/020ab456a0d50aad0b61317e06b2e024e897f677/docs/research/v8-full-view-zk-20260912/evidence/r17-compact-prepare-svm-r36.jsonl

Inspected algorithms (retained as sources / adapted by staged generators):
- tools/r17_fast_g.rs, blob edd548f97a623c6872a4f37aeb93689dd2c291b5
- tools/r17_fast_g_generate.rs, blob 74ee24922b960bb540a56dee34f35b13cf6638ff
- tools/r17_hybrid_merge.rs, blob eb5f001e9fb6d488c146b5f9cdc7cac3643c82af
- tools/stage_r17_fixed_fft.py, blob debb38ec9d8fd1904163d88b46b1cf268dacde31
- tools/r17_owned_weights.rs, blob 5b0c0dac23abdbdc333a84961f66f77d4091e325
- tools/r17_weighted_groups.rs, blob 5822d40b3a24e76fe7d77d3a424068d17ad1d8c1
- tools/r17_host_relation.rs, blob 8eb134ad7d811a7ab3e48c69af5699f997b474ce
All tool paths above are under docs/research/v8-full-view-zk-20260912 at the initial inspected revision. R36 staging changes must be composed, not overwritten by these older template files.

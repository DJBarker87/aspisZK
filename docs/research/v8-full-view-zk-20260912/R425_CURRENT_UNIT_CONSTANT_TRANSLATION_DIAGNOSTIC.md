# R425 unit-constant interpreter diagnostic

The R425 Aeneas build compiles the reviewed zero-operand unit-constant helper and its evaluator integration. Two focused native fixture runs on the exact R419 LLBC passed: the unit-value fixture reported 11 assertions, and the evaluator fixture reported eight checks. The latter also emitted the expected unsupported `((),)` constant diagnostic twice at `core::iter::traits::iterator::Iterator::try_fold` source span `iterator.rs:2486:4–2490:35`. These are finite OCaml fixture observations.

The R425 main executable built successfully. Its one recorded translation attempt used the unchanged R419 candidate LLBC, R396 baseline, selected batch root, and prepared flags. Translation exited 2 before producing Lean source or a JSON manifest, with `Can't copy a mutable borrow` at the `Iterator::next` call span `iterator.rs:78:4–78:45` (compiler `interp/InterpExpressions.ml:234`). The failed translation has no Lean axiom report. OCaml build and fixture phases likewise have no Lean theorem axiom report.

This diagnostic records helper/integration compilation, finite fixture behavior, main executable compilation, and the translation frontier. It proves no Lean theorem and no Rust-to-Aeneas or callback execution correspondence, source security, or end-to-end behavior.

The next unresolved source obligation is faithful handling of the actual mutable-reference operand/reborrow at `Iterator::next`, preserving ownership and subsequent iterator state, errors, and callback flow. No generated proof files exist from this translation attempt.

The build and translation source revisions and exact checksums are recorded per phase. The helper build used campaign revision `a3fe5df6b53caa52322339906642de5064fc2bbb`; integration, fixtures, main build and translation used `ee7ba72da456d5f353bca9f6739b23750a5dfffa`. The final binary SHA256 is `eadb205fc1e00cf7e32197dd7cbbbd82aa42b59442d8f186cfdca7c8fdca9b01`. The snapshot toolchain has no Git metadata; exact source and binary hashes pin it.

| Focused phase | Exit | Wall time | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Unit helper compilation | 0 | 7.49 s | 479,152 | 0 |
| Evaluator integration compilation | 0 | 12.71 s | 395,416 | 0 |
| Unit fixture build | 0 | 82.57 s | 590,016 | 0 |
| Unit fixture execution, 11 checks | 0 | 0.08 s | 38,896 | 0 |
| Evaluator fixture first build, private API unavailable | 1 | 0.97 s | 288,520 | 0 |
| Evaluator fixture corrected build | 0 | 1.48 s | 296,544 | 0 |
| Evaluator fixture execution, 8 checks | 0 | 0.13 s | 49,808 | 0 |
| Main executable build | 0 | 1.74 s | 334,792 | 0 |
| Actual-source translation inventory | 2 | 0.77 s | 142,032 | 0 |

The separately preserved execution-launch preflight stopped on a missing optional sidecar before invoking any fixture. The revised launch used the already recorded executable hash. All NUC runs used recorded 5 GiB high / 7 GiB maximum / zero-swap / 128-task caps. Full logs and failure histories are in the accompanying evidence bundle; the metrics above are GNU-time measurements, not wrapper process memory.

Verifier Rust, authentication, canonical checks, negative examples and every security parameter remain unchanged. The genuine 999,790 / 999,532 CU results are preserved; no CU benchmark or unchanged regression was rerun.

Saved-evidence verification: `python3 docs/research/v8-full-view-zk-20260912/evidence/r425-current-unit-constant-translation-diagnostic/verify_bundle.py`. This checks recorded hashes and outcomes and does not replay a build or establish source semantics.

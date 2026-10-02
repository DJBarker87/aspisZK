# R425 unit-constant interpreter diagnostic

The R425 Aeneas build compiles the reviewed zero-operand unit-constant helper and its evaluator integration. Two focused native fixture runs on the exact R419 LLBC passed: the unit-value fixture reported 11 assertions, and the evaluator fixture reported eight checks. The latter also emitted the expected unsupported `((),)` constant diagnostic twice at `core::iter::traits::iterator::Iterator::try_fold` source span `iterator.rs:2486:4–2490:35`. These are finite OCaml fixture observations.

The R425 main executable built successfully. Its one recorded translation attempt used the unchanged R419 candidate LLBC, R396 baseline, selected batch root, and prepared flags. Translation exited 2 before producing Lean source or a JSON manifest, with `Can't copy a mutable borrow` at the `Iterator::next` call span `iterator.rs:78:4–78:45` (compiler `interp/InterpExpressions.ml:234`). The failed translation has no Lean axiom report. OCaml build and fixture phases likewise have no Lean theorem axiom report.

This diagnostic records helper/integration compilation, finite fixture behavior, main executable compilation, and the translation frontier. It proves no Lean theorem and no Rust-to-Aeneas or callback execution correspondence, source security, or end-to-end behavior.

The next unresolved source obligation is faithful handling of the actual mutable-reference operand/reborrow at `Iterator::next`, preserving ownership and subsequent iterator state, errors, and callback flow. No generated proof files exist from this translation attempt.

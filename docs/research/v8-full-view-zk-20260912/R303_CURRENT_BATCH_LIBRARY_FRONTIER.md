# R303 actual batch library frontier

The exact selected batch body was emitted in R292, but its five function templates and Chain type remain unresolved. R294 extracted the requested standard-library bodies with `has_errors=false`; R295 translation then rejected `Try<R>::Output = B` in the generic iterator signature before producing Lean output. R297 specialized the concrete source call graph without changing Rust, removing that constraint, but R303 translation stopped at an erased region in the instantiated signature. No batch execution theorem was proved by these diagnostics.

The original R283 declaration order was already valid. The failed R288/R290 subset-order attempts and all extraction/translation failures are retained. The sole omitted large decoded R280 JSON is retained locally; its exact size/hash and a tested byte-identical reconstruction from the archived original LLBC are recorded.

The [manifest](evidence/r303-current-batch-library-frontier/manifest.json) records every target, source revision/checksum, exit, wall time, peak RSS, swap, cap and precise boundary. No Lean compilation occurred in these stages, so `#print axioms` is explicitly not applicable. No unchanged successful job reran.

Next: prove the isolated actual `Slice.last` and reverse-loop leaves, discharge faithful traversal and shared inversion, then bind full callback chronology and all joint privacy/soundness arguments. R286/R287 field leaves are separately proved and pushed in `b87e6b73671c5bf747de1b0bf3dd324fc428912c`. The end-to-end claim remains open; verifier source, every security parameter and 999,790 / 999,532 CU remain unchanged.

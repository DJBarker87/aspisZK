# Measurement plan and stopping rules

The source-reported final R18 primary consumes 4,781,147 / 4,784,274 CU. Its second complete reference verifier is already excluded in the primary build. The 1.2M and 1.4M runs fail. Source-report numbers are not measurements executed in this packet environment.

The internal opening reference interval is 875,150 CU. Subtracting that interval arithmetically leaves 3,905,997 CU; this is a counterfactual budget, not a measured optimized verifier. Therefore removing the internal reference alone cannot meet the target.

Do not reset to dense G or search for another mixing matrix. Keep sparse G and T163 while testing exact-output improvements. The larger channel-fold trial also keeps this mask map and basis, but changes the protocol and needs its own security ledger.

## Experiment order

1. Same-profile source redundancy proof/control, followed by a primary SBF build that excludes only the proven redundant internal check. Record both witnesses, all negative classes and error ordering.
2. Same-profile shared query accumulator. Check old/new increment bytes, all three folded query states and final acceptance. Measure separately and jointly.
3. Canonical multiplication/word-kernel microbenchmarks under the unchanged checked-release build. Inspect emitted instruction counts and whole-program behavior before selecting a winner.
4. Factored correction, shared factor/geometry reuse, and sparse-G product batching. Compare with the best existing fused implementation, not a deliberately slow reference. Logical product counts are not CU results.
5. New-profile quadratic channel-fold experiment: full source witness/proof acceptance, new-message privacy screening and source extraction obligations, then SBF measurement before lengthy formal expansion. Preserve the best same-profile stage.

For every experiment retain commit/profile, source chain, exact Rust cfgs/features, toolchain/target, ELF hash, fixture hashes, heap cap, frame diagnostics, instrumentation state, primary/reference mode, result code and CU. Reuse the existing isolated source stagers, cached Linux toolchain and bounded zero-swap scopes. Do not modify production code or use wallets/deployment.

Same-profile results use the same proof bytes. New-profile results require fresh proofs; label cross-profile comparisons. A successful host test, an ELF emitted despite a frame warning, a diagnostic high-budget success, or a low CU total ending in failure is not supported-budget verification.

## Where the channel fold can remove work

It replaces two quotient folds per fibre with one, two Final256 arrays with one, two sets of final folds with one, and the A/E split with one ordinary functional with modified point scales. The sparse G functional remains. There is still paired authentication and all-limb decoding. Semantic verification does not disappear. Consequently the proposal does not establish a 1.4M total by operation counting alone.

Prototype costs should be measured at ordinary preparation, semantic rounds/terminal, packed decoding, authentication, quotient folding, query injection/folds, ordinary correction, sparse G and final acceptance. This identifies whether the remaining limit is arithmetic implementation or a genuine architectural cost.

## Acceptance and fallback

The target is a complete primary verifier at the supported budget, with all parser/domain/authentication/relation checks, and explicit outstanding privacy/soundness status. Stop calling the resource problem solved until that execution passes on both genuine witnesses and the invalid suite.

If the best correctly checked prototype remains above the budget, report its measured stage totals and preserve it. Do not keep changing privacy profiles just to improve one benchmark. A checkpointed multi-transaction verifier is a separate operational fallback, not a CU reduction or a single-transaction success. Any such fallback needs sealed proof/context binding, program-owned state, no settlement before all phases, and current-state revalidation. It is not implemented by this packet and must not be substituted for the user's single-budget objective.

# R605 cached field challenge law with explicit loss

For arbitrary initial duplex state, exact QM31 target, and oracle memo table, R605 bounds the difference between the cached-oracle ordinary challenge target probability and R601's exact independent-reply mass by the independent probability that a freshness guard encounters a previously cached address. The guard includes addresses cached before this challenge and those first read during it. The proof assumes no whole-program freshness and retains the sampler's failed outputs. The memoized oracle remains consistent on repeat reads.

This is a quantitative theorem for the existing source-shaped `challengeProgram`. It does not replace the guard probability with a small number, prove a bound for actual prior transcript history, or establish native-source correspondence for the complete callback. The guard is an analytical comparison program, not a change to the selected verifier.

Exact target `AspisV8R19/R605GuardedFieldLaw.lean`; source [R605GuardedFieldLaw.lean](lean/AspisV8R19/R605GuardedFieldLaw.lean), SHA256 `0ed95eb91b6075f9e01a6e95ce422093e8890769db13bff1fb4d1bcdcd5ff450`, source revision `e23f6e2008c98c5d8d0139fe4d967d97b7f1ea64`. Focused attempt `1791092257371920000` exited 0, wall `0:01.23`, peak Lean-child RSS `3266624` KiB, swap `0`. It used the pinned Lean 4.32 cached workspace with `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`.

Complete axiom output:

```text
'AspisV8R19.R605GuardedFieldLaw.cached_field_mass_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The exact source, direct import copies, runner, raw log and receipt are saved in [evidence/r605-guarded-field-law](evidence/r605-guarded-field-law/). One changed target compiled; no unchanged suite or CU benchmark was repeated.

The first remaining proposition is a source-instantiated, causal bound on this guard-failure probability for the actual complete shared-oracle history and sampler stopping behavior. Arbitrary starting states and arbitrary caches can make the guard fail with probability one; a small loss cannot be asserted without the missing history argument. Complete circle/nonzero retry laws, published-view simulation, quotient-pair extraction and all overall security losses remain open. No end-to-end privacy or security claim follows from R605 alone.

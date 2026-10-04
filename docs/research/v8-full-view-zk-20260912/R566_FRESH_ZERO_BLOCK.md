# R566: Fresh squeeze block event law

R566 proves a conditional law for one actual source-shaped duplex squeeze. For any initial transcript state `s` and memo table `t`, if the squeeze address `squeeze (bytes s)` is unread in `t`, then the memoized two-ask `squeezeProgram s` assigns its returned 32-byte block’s first-four-masked-31-bit-zero event mass

`(1 / 2^31)^4`.

The proof preserves the second `advance` ask and its cache behavior. The observer depends only on the first returned block, so an advance cache hit contributes that same event indicator, while an advance cache miss averages the constant indicator over its reply. Both cases reduce to R551’s exact one-uniform-state block mass.

This is a conditional one-squeeze event law. It does not prove that the actual selected callback prefix leaves this squeeze address unread, bound the unread-premise failure across adaptive attempts, establish independence across repeated attempts, or give the probability of the full QM31 challenge returning zero. It makes no end-to-end privacy or security claim.

## Verification

- Canonical source: `lean/AspisV8R19/R566FreshZeroBlock.lean`
- Source SHA256: `29b4b7886e3c114c7f2a2370a71e45fb228d951dc1dc1954e2f3ffb9bb09c490`
- Source revision: `b544f78357c70c99331f42e2edae462f73ad4d47`
- Target: `AspisV8R19/R566FreshZeroBlock.lean`
- Exit status: 0
- Wall time: 1.22 s; peak Lean-child RSS: 3,228,000 KiB; swap: 0
- Scope: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`
- Complete theorem axiom output: `depends on axioms: [propext, Classical.choice, Quot.sound]`
- Direct local import hashes are recorded in the final attempt receipt. R551 V10 is `f99ee19cc9d3a471e1e9768a4bee2001a714e6d085f50885929bbaf1ee3ca2b6`.

All four attempts, each exact source snapshot, complete log, and receipt are in `evidence/r566-fresh-zero-block/attempts/`. Three failed attempts remain preserved alongside the successful attempt; no unchanged attempt was replayed after the final green run.

## Reusable oracle-law boundary

The existing generic `AdaptiveFirstReadLaw.lazyMean_eq_independentMean` applies to adaptive oracle programs when its recursive `FreshFrom` premise is supplied: every reached address is absent before the query, for every answer-dependent continuation. `AdaptiveFirstReadSource.squeezeProgram_fresh_after_trace` proves that premise locally for a squeeze after a supplied trace when the source `Fresh` condition holds. `R453SourceFirstLimbLaw` and `R455SourceRefillLaw` likewise assume their local squeeze and advance addresses are unread. `QueryObservedFreshHistoryLaw` has the same conditional shape for q22.

These lemmas do not establish the required unread-address premise for the complete selected callback chronology, nor sum failure losses over its adaptive attempts. R566 adds the one-output event mass once that local premise holds; it does not close those source-prefix or whole-campaign obligations. The exact theorem sources and SHA256s are recorded in `evidence/r566-fresh-zero-block/reusable-oracle-machinery.md`.

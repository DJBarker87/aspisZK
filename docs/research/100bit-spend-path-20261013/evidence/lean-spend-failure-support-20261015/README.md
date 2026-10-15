# Spend failure support and q22 containment

This focused evidence bundle records `R1SpendFailureSupport`. The module uses the existing `SpendExtraction.large_matching_extracts` theorem unchanged: with its typedness, opening-goodness, accepted-pairing, sumcheck, and candidate-wide outside-bad premises retained, absence of any candidate with both `ProductionHolds ∧ CopyLinkBalance` and `SpendSemantics.NoteFacts` implies matching support has cardinality at most 9557. It then applies the existing `R0C.V3.Q22.q22_bound` uniformly in the initial state.

This is a conditional deterministic support-to-query-law bridge. It does not derive its extraction premises from a transcript, prove D1/D2/D3, establish knowledge extraction or source correspondence, or claim protocol soundness.

The source is [SpendFailureSupport.lean](../../lean/SpendFailureSupport.lean), SHA-256 `694f0b092cd454dac1dbd711586230fd64097ed860a1c560c644588df20d8390`. It was focused-compiled at base revision `a17829a776d533d7cd0beeb1f8676dcc793a909c` with the pinned NUC snapshot runner and 4G/6G/0 swap. The final object archive contains `R1SpendFailureSupport.olean` (member SHA-256 `ea24917230374f2320d7ccaaf252d45461a7b37ca790fcab6c47919ec1309116`).

Attempt `a` failed on unresolved `State`/`indicator` names and the default recursion depth; `b` failed because the local `set_option` command preceded the declaration's attached doc comment. Both source snapshots and raw logs are preserved. Attempt `c` is green (1.67 s, 3,571,084 KiB peak RSS, zero swap) with both public axiom reports limited to `propext`, `Classical.choice`, and `Quot.sound`.

# NLZ fold plan

Target not yet established. Baseline ledger23: 580/0/19.

137 transcription: frozen crates/aspis-r1-cost-probe/src/r1_semantic.rs:311–319, SHA pinned from 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Source folds NLJ_Observed.events_from_cuts and NLJ_Observed source theorems are support only; NLJ_Control137.observed_fold uses a weaker 136 value packet and is not used as a native fold.

087 transcription: frozen crates/aspis-r1-cost-probe/src/candidate.rs:255–264, NLR_Prepare.source and NLR_PrepareInitialized.source cover all source arms. No allocation success inferred from model reserveOk.

ReviewedTranscription entries are proposed option-A P6/D188 reclassifications per (bh), not removals of trust.

Compiled conditional resource-chain projections: NLZ_Segments137.source/fold and NLZ_Segments087.source/fold. One heap is threaded through every cut. Every returned Err and outer fail/div is an immediate terminal with its chronological digest/resource prefix retained. These theorems do not establish a native producer or lawful physical resource transitions: the Occurrence record is still unconstrained beyond its endpoints/trace. They cannot supply a row root or full-strength RowSpec.

Hypothesis review: each fold takes its own Chain, whose value-step equations must be discharged by actual parent segment cuts and CLOSED child packets. It also carries every explicit resource occurrence, which needs frozen-source/allocator interpretation. These are SUPPORT hypotheses; they are outside the admissible positive-root inventory until instantiated. 087 additionally takes cfg, which must be fixed, not exported as free Ops. No new root is emitted. No weaker136 schema appears as a premise of these theorems.

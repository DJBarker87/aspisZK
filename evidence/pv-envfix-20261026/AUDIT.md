# Research / rebuilt env-J source audit

Research revision: `3dbbe11f663278482e9382c451226c2c3fbc3ec8`. Read-only host inventory; no Lean attempts.

## R1Z/SimCostOuterRetry6

Transitive R0Z/R1Z chain (including target):

- `R0Z/AbsorptionLaw` imports R0Z/AffineLaw; source MATCH; shared object present.
- `R0Z/AffineLaw` imports R0Z/StatisticalDistance; source MATCH; shared object present.
- `R0Z/Chain` imports R0Z/Shift, R0Z/TerminalEligible; source MATCH; shared object present.
- `R0Z/D12` imports R0Z/JointTrace, R0Z/AbsorptionLaw; source MATCH; shared object present.
- `R0Z/FsAbort` imports R0Z/FsGood; source MATCH; shared object present.
- `R0Z/FsAbortBounds` imports R0Z/LawTransport; source MATCH; shared object present.
- `R0Z/FsAbortR1` imports R0Z/FsAbort, R0Z/FsAbortBounds; source MATCH; shared object present.
- `R0Z/FsGood` imports R0Z/FsStatement, R0Z/Shift; source MATCH; shared object present.
- `R0Z/FsStatement` imports R0Z/JointView, R0Z/LawTransport; source MATCH; shared object present.
- `R0Z/GoodDensity` imports (no R0Z/R1Z imports); source MATCH; shared object present.
- `R0Z/HelperInvariant` imports R0Z/MaskLayout, R0Z/HonestView; source MATCH; shared object present.
- `R0Z/HonestValid` imports R0Z/SilentReduction, R0Z/FsAbort; source MATCH; shared object present.
- `R0Z/HonestView` imports R0Z/ViewAffine; source MATCH; shared object present.
- `R0Z/HvzkS` imports R0Z/HvzkV; source MATCH; shared object present.
- `R0Z/HvzkV` imports R0Z/HonestValid; source MATCH; shared object present.
- `R0Z/JointTrace` imports R0Z/PayloadSplit, R0Z/HelperInvariant; source MATCH; shared object present.
- `R0Z/JointView` imports R0Z/ZkStatement; source MATCH; shared object present.
- `R0Z/K4` imports R0Z/PureRounds; source MATCH; shared object present.
- `R0Z/LawTransport` imports R0Z/StatisticalDistance; source MATCH; shared object present.
- `R0Z/MaskLayout` imports R0Z/MaskedProtocol; source MATCH; shared object present.
- `R0Z/MaskedProtocol` imports (no R0Z/R1Z imports); source MATCH; shared object present.
- `R0Z/Partition` imports R0Z/JointView; source MATCH; shared object present.
- `R0Z/PayloadSplit` imports R0Z/Partition; source MATCH; shared object present.
- `R0Z/PureRounds` imports R0Z/Shift, R0Z/Chain, R0Z/Z4Maps; source MATCH; shared object present.
- `R0Z/R0Batched` imports R0Z/HonestView; source MATCH; shared object present.
- `R0Z/Shift` imports R0Z/D12, R0Z/GoodDensity, R0Z/LawTransport; source MATCH; shared object present.
- `R0Z/SilentReduction` imports R0Z/K4, R0Z/PureRounds; source MATCH; shared object present.
- `R0Z/StatisticalDistance` imports (no R0Z/R1Z imports); source MATCH; shared object present.
- `R0Z/TerminalEligible` imports R0Z/HelperInvariant; source MATCH; shared object present.
- `R0Z/ViewAffine` imports R0Z/MaskLayout, R0Z/StatisticalDistance; source MATCH; shared object present.
- `R0Z/Z4Maps` imports R0Z/D12, R0Z/Shift; source MATCH; shared object present.
- `R0Z/ZkStatement` imports R0Z/HonestView, R0Z/R0Batched, R0Z/StatisticalDistance; source MATCH; shared object present.
- `R1Z/Batched` imports R0Z/PayloadSplit, R1Z/BatchedAlgebra; source MATCH; shared object present.
- `R1Z/BatchedAlgebra` imports (no R0Z/R1Z imports); source MATCH; shared object present.
- `R1Z/GamesR1` imports R0Z/HvzkS, R1Z/ModelsVR1, R1Z/TranscriptR1; source MATCH; shared object present.
- `R1Z/LensR1` imports R0Z/FsAbortBounds; source MATCH; shared object present.
- `R1Z/ModelsVR1` imports R0Z/HvzkV, R0Z/FsAbortR1, R1Z/Batched; source MATCH; shared object present.
- `R1Z/SimCostOuterRetry6` imports R1Z/SimCostWriter; source MISMATCH; shared object MISSING.
- `R1Z/SimCostWriter` imports R1Z/GamesR1; source MATCH; shared object present.
- `R1Z/TranscriptR1` imports R1Z/LensR1; source MATCH; shared object present.
## R1Z/EventsR1P2

Transitive R0Z/R1Z chain (including target):

- `R0Z/AbsorptionLaw` imports R0Z/AffineLaw; source MATCH; shared object present.
- `R0Z/AffineLaw` imports R0Z/StatisticalDistance; source MATCH; shared object present.
- `R0Z/Chain` imports R0Z/Shift, R0Z/TerminalEligible; source MATCH; shared object present.
- `R0Z/D12` imports R0Z/JointTrace, R0Z/AbsorptionLaw; source MATCH; shared object present.
- `R0Z/FsAbort` imports R0Z/FsGood; source MATCH; shared object present.
- `R0Z/FsAbortBounds` imports R0Z/LawTransport; source MATCH; shared object present.
- `R0Z/FsAbortR1` imports R0Z/FsAbort, R0Z/FsAbortBounds; source MATCH; shared object present.
- `R0Z/FsAbortTape` imports R0Z/FsAbortBounds; source MATCH; shared object present.
- `R0Z/FsGood` imports R0Z/FsStatement, R0Z/Shift; source MATCH; shared object present.
- `R0Z/FsStatement` imports R0Z/JointView, R0Z/LawTransport; source MATCH; shared object present.
- `R0Z/GoodDensity` imports (no R0Z/R1Z imports); source MATCH; shared object present.
- `R0Z/HelperInvariant` imports R0Z/MaskLayout, R0Z/HonestView; source MATCH; shared object present.
- `R0Z/HonestValid` imports R0Z/SilentReduction, R0Z/FsAbort; source MATCH; shared object present.
- `R0Z/HonestView` imports R0Z/ViewAffine; source MATCH; shared object present.
- `R0Z/HvzkS` imports R0Z/HvzkV; source MATCH; shared object present.
- `R0Z/HvzkV` imports R0Z/HonestValid; source MATCH; shared object present.
- `R0Z/JointTrace` imports R0Z/PayloadSplit, R0Z/HelperInvariant; source MATCH; shared object present.
- `R0Z/JointView` imports R0Z/ZkStatement; source MATCH; shared object present.
- `R0Z/K4` imports R0Z/PureRounds; source MATCH; shared object present.
- `R0Z/LawTransport` imports R0Z/StatisticalDistance; source MATCH; shared object present.
- `R0Z/MaskLayout` imports R0Z/MaskedProtocol; source MATCH; shared object present.
- `R0Z/MaskedProtocol` imports (no R0Z/R1Z imports); source MATCH; shared object present.
- `R0Z/Partition` imports R0Z/JointView; source MATCH; shared object present.
- `R0Z/PayloadSplit` imports R0Z/Partition; source MATCH; shared object present.
- `R0Z/PureRounds` imports R0Z/Shift, R0Z/Chain, R0Z/Z4Maps; source MATCH; shared object present.
- `R0Z/R0Batched` imports R0Z/HonestView; source MATCH; shared object present.
- `R0Z/Shift` imports R0Z/D12, R0Z/GoodDensity, R0Z/LawTransport; source MATCH; shared object present.
- `R0Z/SilentReduction` imports R0Z/K4, R0Z/PureRounds; source MATCH; shared object present.
- `R0Z/StatisticalDistance` imports (no R0Z/R1Z imports); source MATCH; shared object present.
- `R0Z/TerminalEligible` imports R0Z/HelperInvariant; source MATCH; shared object present.
- `R0Z/ViewAffine` imports R0Z/MaskLayout, R0Z/StatisticalDistance; source MATCH; shared object present.
- `R0Z/Z4Maps` imports R0Z/D12, R0Z/Shift; source MATCH; shared object present.
- `R0Z/ZkStatement` imports R0Z/HonestView, R0Z/R0Batched, R0Z/StatisticalDistance; source MATCH; shared object present.
- `R1Z/Batched` imports R0Z/PayloadSplit, R1Z/BatchedAlgebra; source MATCH; shared object present.
- `R1Z/BatchedAlgebra` imports (no R0Z/R1Z imports); source MATCH; shared object present.
- `R1Z/CouplingR1P` imports R1Z/GamesR1P, R0Z/FsAbortTape; source MATCH; shared object present.
- `R1Z/CouplingR1P2` imports R1Z/CouplingR1P; source MATCH; shared object present.
- `R1Z/EventsR1P` imports R1Z/CouplingR1P2, R1Z/LayoutR1P3; source MATCH; shared object present.
- `R1Z/EventsR1P2` imports R1Z/EventsR1P; source MISMATCH; shared object MISSING.
- `R1Z/GamesR1` imports R0Z/HvzkS, R1Z/ModelsVR1, R1Z/TranscriptR1; source MATCH; shared object present.
- `R1Z/GamesR1P` imports R1Z/GamesR1, R1Z/LazyFrozen; source MATCH; shared object present.
- `R1Z/LayoutR1P` imports R1Z/GamesR1P; source MATCH; shared object present.
- `R1Z/LayoutR1P2` imports R1Z/LayoutR1P; source MATCH; shared object present.
- `R1Z/LayoutR1P3` imports R1Z/LayoutR1P2; source MATCH; shared object present.
- `R1Z/LazyFrozen` imports R1Z/LazyTable; source MATCH; shared object present.
- `R1Z/LazyTable` imports R0Z/FsAbortBounds; source MATCH; shared object present.
- `R1Z/LensR1` imports R0Z/FsAbortBounds; source MATCH; shared object present.
- `R1Z/ModelsVR1` imports R0Z/HvzkV, R0Z/FsAbortR1, R1Z/Batched; source MATCH; shared object present.
- `R1Z/TranscriptR1` imports R1Z/LensR1; source MATCH; shared object present.

## Exact source mismatches

- `R1Z/EventsR1P2` research `5746651a999f4f7cec78c99d314627f50e26a1e1c4039825a54f79a735fd5893`; rebuilt `536e5032a81eea01b6ed02040e715dfc6929b877aac7d950826b8d3e4c9bfe42`; EJR [(30485, '536e5032a81eea01b6ed02040e715dfc6929b877aac7d950826b8d3e4c9bfe42')].
- `R1Z/SimCostOuterRetry6` research `bfddad153bd3d7a3c3b111730b76f3aac66ea7706ae37a65742d6242c8f6996b`; rebuilt `62749afa1a7a19d771c18a68a01024d791d3b61c5f0f5cda198714717beec21f`; EJR [(30431, '62749afa1a7a19d771c18a68a01024d791d3b61c5f0f5cda198714717beec21f')].

Missing objects: `R1Z/EventsR1P2`, `R1Z/SimCostOuterRetry6`

Full per-module hashes, sent ledger entries, EJR source hashes and import adjacency: `audit.json`.

## Diagnosis before any proof edit

Both failures used stale target sources, not stale R0Z/R1Z dependencies.
Every strict dependency's rebuilt source and EJR recorded source hash matches
research HEAD. The only missing chain objects are the two failed targets.
The sent ledger additionally records the same stale SimCostOuterRetry6 source
at historical attempt 8828. No other sent hash in either chain mismatches.
`effective_objects.json` inventories all search-path objects: shared objects
win and no conflicting variant is present for any module in either chain.

The stale SimCostOuterRetry6 text contains precisely the two failing omega
calls and the failing zero-case `Nat.le_refl`. Research already replaces
those with Fin.not_lt_zero, Fin.succ_lt_succ_iff and explicit simplification.
The stale EventsR1P2 text uses card_subtype_compl / card_eq_one_iff, while
research already uses Subsingleton Fintype transport and Equiv.optionSubtypeNe.
Exact before/after text is retained in the two `.diff` files. These are
historical differences, not edits made by this job. Existing theorem statements
are unchanged; research additionally has the generic card_NZ_of theorem.

Plan: compile both research target sources byte-for-byte into the private
job objects; no dependency recompilation is indicated by this inventory.
No unchanged retry of either historical failed source is proposed. If research
EventsR1P2 fails, isolate with PV_Env_ prefixes before further attempts.

Host directory created: /home/dombarker/project-offloads/codex-pv-envfix-20261026.
No proof source or shared host source/object/launcher has been changed.
The shared launcher currently hardcodes shared output paths; private launcher
routing clarification is pending before any compiler invocation.

PrivacyR1HeadlineDeployedReal.privacy_headline_deployed remains conditional:
zero premises removed, added or changed by this diagnosis. Target not yet
established. This is source/cache provenance evidence, not a release replay.

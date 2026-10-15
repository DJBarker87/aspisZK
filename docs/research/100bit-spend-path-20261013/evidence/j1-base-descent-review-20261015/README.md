# J1 base-descent artifact review

This is a read-only artifact and provenance audit of the eight focused Lean targets listed below. It records source/receipt/object consistency and axiom output; it is not a mathematical review or a release-gate assessment. The inspected source base is `c7b5a949e2274b15ac91a6299fbbc3da691aeb3c`. Machine-readable details are in `review.json`.

The audited targets are `R1ExactBaseProjection`, `R1SpendDataMap`, `R1SpendRelationMap`, `R1SemanticPayloadOpeningView`, `R1CandidateBaseProjection`, `R1SpendBaseDescent`, `R1TraceSpendWitness`, and `R1ConcreteSpendExtraction`. They are stored in seven bundles because SpendBaseDescent and TraceSpendWitness share one bundle. For all eight, the final local source matches the green attempt digest and the recorded axiom outputs contain only standard axioms. The bundles preserve failed attempts and source snapshots; checksum and archived object checks are recorded per bundle in `review.json`.

The final `R1ConcreteSpendExtraction` attempt e passed in 2.29 s with peak RSS 3,554,160 KiB and zero swap under the 4G/6G/0 cgroup. Attempts a–d remain recorded as failures. Its final source and direct-import objects are archived and hash-checked.

The observed `R0P.SemCharP` cache issue is retained as provenance context. The repository and historical generic-workspace source have the same SHA-256 (`e31f972835a430f019d8d05995add7923e65282cf71ba957f4534bcaad10aa42`), while the object used by failed attempt d came through a symlink to the generic workspace and had SHA-256 `29848de9b60311ebf7c598e3a67f66de2642c5b2bbee3cffadbc844c8070a903`. That attempt reported unknown constant `AspisV5ComponentCQM31TowerExact.QM31Exact`. Green attempt e does not import SemCharP and proves the characteristic argument against the current tower directly. This records the observed compile/cache boundary; it does not claim that the historical source differed.

These results establish focused Lean artifacts and their recorded provenance. They do not establish Rust/source refinement, a complete protocol proof, or a security conclusion.

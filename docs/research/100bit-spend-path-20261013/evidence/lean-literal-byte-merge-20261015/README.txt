LiteralByteProtocol merge replay — J1.R10

Merge parents initially f952c6cf849d3ae181c9fecf5a637d7e5429c389 and
7c5ca86991e45c33f3eb7b34cd34ccda5e71d620. Remote advancement 9ac54d0ec
adds only new files and does not change this source or importer closure.

The merged protocol has an optional extractor parameter. Omitting it selects
GenericNoHit.chooseWitness as before; supplying it retains the raw-byte
conditional theorem API. State/rows/d1/d2 and the explicit-extractor transcript,
chain/read and conditional-bound declarations all remain. D1/D2 specialize to
the default specification extractor and do not establish efficient extraction.

Exact reverse importer closure: LiteralByteProtocol, LiteralByteRunFacts,
LiteralOpeningRunGood. The importer sources are unchanged. Only the protocol
source is a merge resolution. Sources/objects and focused receipts are retained.

Environment: local Lean 4.32.0 through /Users/dominic/ZK/AspisFormal lake env;
-M6000, one focused process group at a time, 7 GiB aggregate RSS kill threshold.
No package-wide build, manifest replay, or build-host Lean job ran. Sources
were checked against retained dependency receipts/snapshots; dependency objects
are a reused pinned cache, not a newly bootstrapped proof release.

The first two protocol attempts failed on missing cache imports, before proof
checking. Twenty-one missing dependencies were restored from tracked archives.
A read-only SSH cache-copy attempt timed out. Six small missing predecessors
were therefore recompiled locally: SubfieldBatch as R1SubfieldBatchStage2,
ResidualBatch, QueryAccumulator, NaturalEmbedding, QueryResidualBridge and
RawPairing. Their exact checked sources and objects are also retained. Early
runner scope text saying no dependency build means no cold/package dependency
build; these six focused predecessor replays are explicitly recorded here.

Per-target exit status, wall time, sampled aggregate peak RSS and source SHA
are in attempts/*.json; /usr/bin/time RSS and swap are in matching logs.
Axioms are extracted to axioms.txt. All three required targets passed. Their 12 axiom reports contain only
subsets of propext, Classical.choice and Quot.sound (firstCell_map has none).
The six predecessor checks also passed with standard axioms. All logs report
zero swaps; no memory threshold was crossed. Final target results:

R1LiteralByteProtocol.lean: exit 0; 65.203 s; peak aggregate 4271184 KiB.
R1LiteralByteRunFacts.lean: exit 0; 81.504 s; peak aggregate 3852112 KiB.
R1LiteralOpeningRunGood.lean: exit 0; 38.006 s; peak aggregate 5056704 KiB.

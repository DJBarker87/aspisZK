# Stage 2: current reader parent, same bytes and six physical reads

`Port4A_NativeReader` is generated from the retained current successful Charon/
Aeneas emission (exact spans, source/module hashes and every substitution in
reader-emission.json). Its parent retains current wrapping subtraction. Decoder,
comparison, header-any and mapped-allocation children are explicit ResumeOps
leaves. No axiom/template is imported. The generator factors the digest-free
tail; this is a source split, not an invented decoder postcondition.

`Port4A_ReaderNormalize.source` proves FULL Result equality to resumeWithOps
for those same leaves given only checkpointSize>=32 on successful size returns.
It includes error/rejected-prefix control. `checked_sub` discharges current
wrapping versus retained checked subtraction after the size guard. No global
checked/wrapping identity or arbitrary success premise is assumed.

`Port4A_ReaderInstall` instantiates retained CheckpointBytes4Ops helpers and
proves sizeBound for every variant, exact reader/reference Result equality and
SAME returned Prepared/Accumulator source transport. This installs current
PARENT CONTROL with retained helper content interpretations; it does NOT yet
identify each child with its current native std/codec/runtime implementation.
The older Kani005/008 timeouts receive no credit and were not rerun.

`Port4A_CheckpointRows` composes the same returned writer Vec with that reader.
Its combined_run has no state provenance premise. fields_and_reads retains
explicit caller/ROM and S1S7S8StateProvenance for exact mathematical BodyMatches
and six model reads; these assumptions are NOT discharged here.

`Port4A_PhysicalReads.six_reads` separately proves exactly six PHYSICAL ordered
reads and same-byte composition, with the actual returned p/a and no mathematical
state/canonicality/ROM/provenance premise. The last three calls carry the existing
Tx2ResumeDigests.Calls witness indexed by the very same saved checkpoint.
It does not assert the checksum address's frozen2 body before provenance.

`Port4A_Parents.installed` changes only op18 in the inherited native-writer-shape
dictionary; op8 remains explicitly reference. `prefix_iff` derives TX1 prefix
preservation from small generic `Port4A_PrefixReader.prefix_iff`.

Accepted current sources:005 nativebody,007 normalization,011 reader installation,
013 combined fields/read join,017 small prefix update,019 physical read trace,
020 dictionary. Full exact timing/RSS/revision/dependency/axiom fields are in
receipts; all exits0, swap0, only standard axioms.001/004/006/008/010/018 were
elaboration failures, preserved and excluded.003/009 were successful predecessors.
014 aborted on internal memory, exit134,7.975592s,RSS4506684KiB;016's isolated
large-dictionary reflexivity proof failed kernel memory,exit1,4.467077s,
RSS4506264KiB. Neither unchanged job was rerun or cap raised. Replacement017
proves the generic record-update fact FIRST, then020 instantiates it.015 never
entered Lean (missing unbuilt Parents dependency); its reservation is not counted.
No failing/sorry-bearing object is imported by accepted sources.

Shipped source, feature/wire/parameter/artifact pins unchanged. No ELF rebuild,
Rust/Kani invocation, source adoption, key operation or push. Focused development
checks do not establish the complete S2 security target or deployed reader port.

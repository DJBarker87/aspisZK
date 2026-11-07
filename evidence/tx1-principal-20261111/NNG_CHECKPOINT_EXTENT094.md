# Checkpoint public-byte extent — caller-domain gap

This is not a new full RowSpec094 impossibility claim. F9 resolves the old parseShape contradiction.

`NNG_CheckpointExtent094` (L668) checks four exact facts against F9: (1) no installed checkpoint observation exists when public_bytes.length≠1880, including abort; (2) Domain094 is invariant under arbitrary replacement of public_bytes; (3) empty public_bytes therefore forbids every checkpoint observation at every Prepared/Accumulator pair; (4) the retained CLOSED writer sourceProgram equality accepts arbitrary stored/public Slice inputs given only the same record WriterDomain. All use standard axioms; exit0,20.782s,6791232KiB,swap0.

Frozen emitted tx1 reads public_bytes first at its checkpoint call (`NMT_lean/NMT_tx1/Funs.lean:255`). Every earlier call, guard and read is independent of that buffer. `LIBC_CheckpointDomain.Domain` adds proof57607/public1880 on top of DriverEstablishedDomain, while `NHS_CheckpointPacket.source` exports its writer equality for all stored/public slices. The separate public_ semantic carrier does not constrain public_bytes.

Exact unresolved obligation: at a reached checkpoint call, discharge the public_bytes1880 conjunct from Domain094 and the SAME prefix, which has not inspected public_bytes. No free prefix-success or actual full-parent counterexample is asserted here. A total checkpoint field retaining the same writer/refinement for arbitrary hash inputs appears necessary. Library-owned change requested asynchronously; no LIB/RSL/source edits made. Independent call/source proofs continue.

L677 `NNG_ReturnedExtent094.required` strengthens the finding: EVERY successful returned observation of the installed whole Ref094 implies public_bytes.length1880. It follows by source-order inversion of the relational bind, preserving stopped/error distinctions, and extracting the SAME checkpoint domain. Exit0,23.712s,6794548KiB,swap0; standard axioms. It does not assume or construct a successful whole-parent execution.

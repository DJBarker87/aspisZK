# Mutable flush ABI

`Port4D_FlushABI`, `Port4D_FlushStep`, `Port4D_FlushLoop`,
`Port4D_FlushResult` prove symbolic termination and exact deferred back-write
of the CURRENT emitted parent, including the new outer enumerate closure.
`reference_eq` compares COMPLETE Results on destination.length<=raw.length;
`vec_backwrite` handles the actual stage Vec deref_mut/back closure.
No concrete64-row normalization is used.

Discharged: current deferred function-returning traversal versus the retained
S8 eagerly applied iterator result; source-type carrier transport; Vec ABI.
Retained: TrustedStd mutable iterator content/runtime interpretation and the
explicit retained reducer value child. This is NOT yet a proof that a different
native value extraction satisfies that child; a local S5 reducer port is needed.
Caller raw phase/row trace and field meaning are separate from this ABI result.
No whole-flush agreement premise is used.

Accepted targets: lean001 ABI,002 step,004 loop,008 result; all exit0,swap0,
standard axioms. Exact target/command/source revision/source and dependency
hashes/wall/RSS/full axioms are in each receipt. lean003,005–007 are excluded
elaboration errors with source snapshots; no failed object is imported by a
successful downstream target. No timeout, memory kill, cap increase, Kani,
ELF rebuild, or full manifest replay. Budget8/100 Lean,0/60 Kani.

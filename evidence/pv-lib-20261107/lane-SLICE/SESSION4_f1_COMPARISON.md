# f1: frozen statement comparison (session 4)

Module: lean/PV_LIB_SLICE_Spec_f1.lean; focused attempt 49935.
Pre, Post, MachineSpec and Contract : Prop are elaborated; Contract is unproved.
Source/provider cohort is STX 3eb0cb97b63aaf110327a99529cbbca93c670dca;
frozen prose is lane SPEC a84dc05c68e, PSPEC_COMMON revision 2 / SPEC-C2.

The package has no complete f1 row contract. This statement forwards the same entry array to emitted f2 and requires all sixteen destination Vecs in source order, including their lengths, ownership and entry bytes. A later failed allocation ends at its exact first boundary with earlier events/effects retained; success cannot be reported for a partial array or sixteen empty Vecs on a positive input.

Common package comparison: first own completion/fault/actual consumed pending
is used, never execution into lower caller code. Pending requires no completed
frame and no resolved BODY. Infinite behavior retains every observable finite
prefix. Exact full Result payloads, world and ordered events are fixed by the
named source execution. Abort observes only events. Lower and suspended
continuations and all pre-existing source/heap data outside the actual mutable
argument roots and fresh allocation intervals are framed. Entry carries typed
initialized non-null aligned bounded references, registered ownership and live
numbering. No future read, decoder success or successful child premise occurs.
Activation counters are abstracted in observation, never equated across calls.

MachineSpec is over an arbitrary machine and reuses the existing named
OWNER/copy/set_len carrier, program table, handler and zero-cast interpretation;
allocation and reservation channels are explicit. It does not assume this
Post or a child Contract. Named primitive adequacy/bindings, D877 summary graph
transport and frame preservation are later proof obligations. Their absence
is not a missing statement. All allocating transitive bodies, null/layout and
abort branches remain in the source reference, rather than a blanket abort.
Nothing here closes a ledger row or supplies an endpoint premise.

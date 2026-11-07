# f13: frozen statement comparison (session 4)

Module: lean/PV_LIB_SLICE_Spec_f13.lean; focused attempt 49926.
Pre, Post, MachineSpec and Contract : Prop are elaborated; Contract is unproved.
Source/provider cohort is STX 3eb0cb97b63aaf110327a99529cbbca93c670dca;
frozen prose is lane SPEC a84dc05c68e, PSPEC_COMMON revision 2 / SPEC-C2.

The package has no full f13 Pre/Post contract at the frozen pin; its allocator, borrow and prefix helpers are supporting statements. This statement binds the actual Vec descriptor argument at entry and requires a distinct owned clone with final length and entry bytes, preserving source descriptor and allocation. It rules out shallow descriptor copying. Common clauses are defined once in PV_LIB_SLICE_Statements within this module. Attempt49925 omitted classical decidability for least-boundary selection; the corrected declaration compiles49926.

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

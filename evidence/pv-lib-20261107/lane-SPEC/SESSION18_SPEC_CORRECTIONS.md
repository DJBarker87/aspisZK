# Session18 corrections — D1007 / thread-29′

## SPEC-C13 rebase (approved D1007)

Before: Entry14 run112; no coordinate satisfies the adopted native pair law.
After: EntryWorld18.Entry requires the complete OwnInit.Pre, actual registered
run = scopeEntryRsp+120, finite initial stack grant, nonwrapping bounds, full
360-byte prologue space and initialized ACTIVE. No later success is assumed.
The original definitions remain unchanged. Concrete inhabitant/proof receipts
are listed in the session status; intermediate failures earn no credit.

## SPEC-C16 — stack grant overlaps the retained Packet malloc

Before candidate: parent4096, scopeEntryRsp4088, run4208,
stack grant [3584,4608). SuccessSchedule12.pointer 4963 48 = some4096,
so the proposed static stack overlaps Packet [4096,4144).
This is a NEW ENTRY-FIXTURE mismatch, not a contradiction of the existential.
The Rebased*18 modules retain their checked local capture/Pre results only.

After candidate: parent1024, scopeEntryRsp1016, run1136, n1088, F1128,
stack grant [512,1536). Same adopted site offsets112/64/104, source input,
v2 step, native replies and allocation schedule. All scheduled heap allocations
are at or above2048. Disjoint*18 rebuild the full entry on these coordinates.
No frozen row, source implementation, endpoint premise or T field changes.

## SPEC-C17 — counter-sensitive boundary observation in the new C14 draft

BEFORE: ContextMachine18.observe returned Observation.state Execution, retaining
nextActivation and origin lists at a row interface. This violates thread-27:
a D877 contracted call and its expanded execution can advance the counter by
different amounts. It also unnecessarily equates internal native histories at
row boundaries. ContextCounter18.old_distinguishes checks counters4/5, and
sample_numbered/sample_owner establish the relevant local machine invariants.
This is a statement error, not a negation of the full joint existential.

AFTER: ContextCounter18.observe uses EXISTING Frontier.observe/ThreadContract
.observe by name. It retains source cells, control, worlds and events, abstracts
nextActivation, and keeps panic/abort observation to events. The unchanged row
Frame clauses carry Numbered. ContextFinal*18 replace the C14 draft's behavior
comparison only. The full context MACHINE and all concrete history/transport
proofs still preserve complete Execution records; no projection is used to
transport a successor machine. Old frozen and new draft modules remain intact.
Every final row exports CounterBefore and the literal original Pre comparison.

Audit55494 was stopped for this review: EXIT241, wall4:54.55,
peak7002088KiB,swap0. It earns NO PASS. A fresh audit of the changed final roots
is required; this is not an unchanged regression. Caps are not raised.

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

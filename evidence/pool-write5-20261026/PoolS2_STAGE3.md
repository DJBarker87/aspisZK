# Stage 3: original-entry partial composition, not P1 closure

Source anchor 82530662314e70f08519ef1ffd7319a747a500b4 plus snapshotted PoolS2 modules. L032–L061 contain focused compile receipts, including failed predecessor source versions. All current modules through EntryMaster have successful receipts and standard axioms only. No shipped inputs changed; no ELF/release replay.

`PoolS2_EntryMaster.accepted` derives from ONE accepted partial owned value/error stage: the decoder consumes original entry slot-0 bytes, its returned full canonical master supplies the actual mint/bump in the SDK create call, its pool identity equals the original key, and slot-0/slot-9 underlying data cells differ. The latter follows from the same accepted full-byte unique-key prefix and entry alias coherence, rather than an independent separation hypothesis. Master metadata, signer, decode and address checks are source ordered; all outer failure/divergence values are retained.

This is explicitly an owned reference stage. Native AccountInfo-to-owned snapshot, allocator/Box, borrow cleanup, mutable System CPI, planner alias/lanes, final action and write coupling are NOT supplied. Actual decoder and SDK PDA children remain arbitrary named functions; no successful-child law is a field, but their native execution/query interpretation remains open. The new stage removes independently successful prefix/master calls only INSIDE this reference model; no soundness ledger row is discharged.

AENEAS007 isolates original master decoder/Box wrapper: SymbolicToPureValues.ml:878 failure. AENEAS008 changes original planner MIR representation: InterpReduceCollapse.ml:1991 failure. AENEAS009 isolates validation but its unrelated digest loop fails TypesAnalysis.ml:372. CHARON010/AENEAS010 further isolate original master/policy validation and succeed; pure std leaf implementations/refinement are next. No unchanged failed command was retried and no cap was raised.

Budget after L061: 61/100 Lean attempts, 25/25 Kani runs (15 pass). Kani exhaustion has not stopped Lean. Target `PoolS2_Write.accepted_p1_writes_planned` is not established. No accepted attacker-chosen checkpoint write found.

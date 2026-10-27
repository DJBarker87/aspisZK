# Stage 3: valid sufficient event direction

SCJ_Projection.event_implies (SCJ_OrderedTransport.lean) is checked in SCJ_011.
For consistent projected/full traces in the SAME H, read inclusion plus
FIRST-occurrence order preservation imply the exact release event direction.
The FULL log's first-read budget is sufficient. No extra loss is introduced.
SCJ_AccountProjection.event_implies (SCJ_013) instantiates the two concrete
F3X/SCE recorder programs, and obtains the full Q0+Q1+2965 cover directly from
SCF_Charge.charged. Read inclusion and first-order preservation are explicit
remaining implementation obligations. No account instance is manufactured.

The proof uses SCJ_FirstHitWitness.witness, SCJ_BeforeTable.extension and
SCJ_TableExtension.bad. A projected hit is transported at its actual FIRST
read with a larger full table. SCJ_OrderObstruction.sublist_not_first_order
checks exactly which property fails in the retained deletion witness.
SCJ_FirstRead.cached_interior proves safe removal of an interior cached read
with its actual cached answer, for any bad predicate and suffix.

All successful statements in this stage have only standard axioms. SCJ_005
and SCJ_010 are retained local parser/name failures; repaired SOURCES were
compiled in SCJ_006 and SCJ_011. No unchanged failure replay or cap increase.
No timeout, memory kill or package replay.

The actual Rc8 endpoint is still unchanged; no ledger row is removed or
added. The missing order/read inputs are NOT added as new release premises.

# R435 native helper source-shape audit

This read-only check compares selected statements in the R435 helper-guard draft with the structured Fun114/Fun115 rows emitted in `R434ActualFoldUbHelpers.llbc` (SHA-256 `7c03a7576da2d380749bdd48a9ded791e4563d6fb3b6834ef4d15665f479b96e`). The complete rows, signatures, spans, and control-flow arrays remain in the R434 inventory. The exact checks and retained statement fragments are in `source-shape-comparison.json`; `verify_source_shape.py` reproduces the checks against the pinned capture.

The draft's Fun114 claim uses an abstract `Ge` comparison. The native row assigns a `Ge` over copies of local 1 and local 2 to local 3, then switches on a move of local 3. Its full alternate branch is preserved in the comparison record.

The draft's Fun115 claim refers to casts and checked addition. The native row converts copies of locals 1 and 2 from Usize to U64 at top-level statement indices 7 and 9, moves locals 8 and 9 into `AddChecked` at index 10, then copies tuple field 1 from local 7 into local 6 at index 13. Statement 15 switches on a copy of local 6: the first branch's statement list is empty and the alternate branch ends in `Return`. The subsequent top-level statements are separately retained as the failure tail and end in `Abort UndefinedBehavior`.

These are AST shape checks only. The audit does not establish that the AddChecked tuple flag equals the Aeneas `UScalar.overflowing_add` flag, nor that either branch corresponds to an abstract rejected continuation, panic, or execution result. It does not use the draft's bound premise to claim behavior of the native helper.

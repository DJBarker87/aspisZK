# Retained approaches and failures

Initial new synthetic suite on ed58077458: 12 tests, exit 1, three failures.
Synthetic memory.stat was terminated twice, introducing a blank line rejected
by reviewed pairs(). This was a fixture error, not a relaxation opportunity.
Correct fixture emits exactly one LF; old raw scanner is unchanged. All initial
logs/receipt retained. Denial tests are rerun with valid fixture baseline so
malformed fixture cannot mask control/PID checks. No resource failure, host
access, attempt charge, scope or marker occurred. Historical failures remain
immutable and are assessed in ResourceAdmit-SOURCE-ASSESSMENT.md.

Extended denial replay suite on bbf18ea723: 15 tests, exit 1, one failure.
The replay preserved errno/text but named its replay subclass RecordedError,
while the new report also records exception type PermissionError. Decisions
both DENY; full report byte equality correctly failed. Replacement gives the
replay subclass the original errno-derived exception class name, preserving
both error text and recorded class identity. No input or evaluator relaxation.
Initial extended log/receipt retained; changed replay and missing successful
error-path evidence justify the next focused run. No host attempt occurred.

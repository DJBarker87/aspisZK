# Retained approaches and failures

Initial new synthetic suite on ed58077458: 12 tests, exit 1, three failures.
Synthetic memory.stat was terminated twice, introducing a blank line rejected
by reviewed pairs(). This was a fixture error, not a relaxation opportunity.
Correct fixture emits exactly one LF; old raw scanner is unchanged. All initial
logs/receipt retained. Denial tests are rerun with valid fixture baseline so
malformed fixture cannot mask control/PID checks. No resource failure, host
access, attempt charge, scope or marker occurred. Historical failures remain
immutable and are assessed in ResourceAdmit-SOURCE-ASSESSMENT.md.

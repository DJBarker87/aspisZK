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

## Single live attempt: environment pin drift before actual GO

Coordination became terminal before a wait: PID absent, exact output final line
codex-exit=0. Read-only inspection, fresh owned stage and stage-preflight were
successful. One local ATTEMPTED sentinel charged before SSH. The single Q=4GiB
prospective pair passed, with no collection failures. systemd-run requested one
resource-admit-20261024.scope with High3G/Max4G/Swap0/Tasks64. Its child reached
verify(manifest) and raised ValueError: environment differs from allowlist pin.
Full scope.stderr and source bytes are retained. The exact differing variable
or value was not captured; do not speculate that a particular systemd variable
caused it. The scope runner exited 1; parent terminal SCOPE_EXIT exit 78.

No go-pre-pins, go-controls, inside-scope ordered/report, go-exit or marker was
created. The check occurs before actual GO/control capture. Thus effective
scope controls, cgroup peak, swap counters and actual identity/frontier binding
are N/A, not inferred from argv. No claim of actual GO DENY from collected
snapshots: actual GO did not execute. No cap raise, source/env repair, alternative
size, repeat admission or further host inspection. Only own retained capture
export followed. No workload or allocation probe ran. Live budget exhausted.

Unchanged prospective source/runtime/allowlist env pre/post pins match. Stage
preflight also matched. The full new ordered trace replays exactly (14866 events,
original raw input/report hashes). actual-audit.log PASS refers ONLY to this
prospective trace and artifact hash checks; it is not a successful live rehearsal
or actual scope/control/GO gate. The missing actual phase is explicitly retained
as the terminal blocker here and in REPORT. Old audits/denials stay unchanged.

# Own runner correction

L001's own initialization copied S2W_lean_host.py without its unchanged
S2W_run_host.py companion. The admitted scope exited2 before Lean. No compiler
receipt exists; LPq_L001_NOT_RUN.json records unknown metrics as null.

LPq_build.py corrects this by copying BOTH byte-identical existing backends and
checking existing copies before reuse. It also batches transport into admission,
source/config upload plus submission, and read-only receipt recovery. This is
this job's runner, not a changed shared admission/launcher/shim. Validation stays
at least as strict: exit0 AND allowed:true, exact caps, same unchanged backend
source/hash/dependency/metrics checks, library object hash pins, no submission
retry, and bounded60s pre-launch/read-only transport retry. No cap, timeout or
proof-domain change. L002 reached Lean and rejected only an unknown #print name;
its source and full diagnostics are retained. It is not a passing proof audit.

L003 rejected symbolic nominal-field proof attempts: the frozen P constant is
irreducible, so definitional comparison did not identify it with the explicit
cohort constant, and one proof hit the default recursion limit. L004 splits out
scalar namespace equalities with explicit constant rewrites. No recursion or
heartbeat option is raised. All error-recovery sorryAx prints are excluded.

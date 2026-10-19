# Extractor cost composition packet

Schema: `focused-extractor-proof-packet-v1`.
Status: **draft, uncompiled, blocked by local preflight**.

This packet contains planned commands and actual preflight observations, not
successful compilation receipts. `exit_status`, wall time, peak RSS, process
swap, and `axioms_result` are null because **no Lean process ran**. The listed
standard axioms are expectations only, not audit results.

The binding instructions in
`/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/local-lean.txt`
require at least 10 GiB free + inactive memory and a shared `flock` before each
compile. The recorded memory check fails; `flock` is also unavailable. No
process belonging to another task was stopped or modified to reclaim memory.

`manifest.json` pins the source revision, new module hashes and direct import
source hashes. Each module directory has `command.json` (not executed) and
`receipt.json` (blocked). `preflight.json` and `vm_stat.txt` are actual resource
observations. The planned object directory is private; no objects are committed.

When the environment satisfies the gate, compile `RawExtractorCostLedger`
first, then `RawExtractorCostComposed`, under the shared lock with Lean 4.32,
`-j1 -M4400 -DElab.async=false`, and `/usr/bin/time -l`. Recheck memory before
each command. Commands use the supplied reference packet's LEAN_PATH plus
the private objects and the retained GCD-bound cache. Validate cached imports
against the source map before treating a replay as release evidence. Capture
all `#print axioms` output and replace null results with real receipts.

The draft proposes a conditional cost/failure theorem for the exact no-model
failure experiment. Actual implementation instrumentation, scheduling,
normalization/interpolation/list overhead, log reconstruction, and bit-cost
adequacy remain named hypotheses. See
`../../design/M10-EXTRACTOR-COST-20261019.md` for component statements and the
explicit polynomial. This packet does not close M10 or certify a release.

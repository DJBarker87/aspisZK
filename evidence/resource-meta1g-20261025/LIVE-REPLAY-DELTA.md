# New-data replay harness assessment

The six identity-only LIVE-EVIDENCE helpers remain exact to the committed seal.
LIVE-EVIDENCE-replay.py is the retained historical harness reference, never run.
LIVE-new-data-replay.py is a separate local evidence harness for the new capture.
Its ordered-event consumption, corrected Linux errno preserving exact retained raw
error text (no Darwin strerror), collector, full serialized report comparison,
file/runtime/env/limit pins and source-extracted check_controls are unchanged.
No collector, API, policy or evaluator source/operational bytes are changed.

Explicit before/after harness assertions, not theorem/policy premise changes:
- Historical separate evaluator call requested4GiB prospective /0 inside -> this
  epoch's authorized1GiB prospective /0 inside. The collector already uses1GiB.
- Historical GO_DENY/78/absent marker/fixed552960B shortfall -> captured new
  GO_MARKER_PASS/0/present marker; no fixed margin injected into the evaluator.
- Historical evidence filenames -> distinct LIVE-new-data evidence filenames.
Additional evidence assertions check29-name complete inventory programmatically,
marker actual PID/starttime/cgroup + source/report pins, exact768M/1G controls,
55GiB projected ceiling,7GiB reserve,2GiB guard and sampled guard bounds/errors.
These assertions verify the claim against inputs; they do not supply inputs to the
collector. All ordered inputs consumed, full outputs compared. Failed assertions
are terminal local evidence failures and retained; no remote repair is possible.
The measured wrapper records hashes of the actual new-data harness. The immutable
helper copy and independent source review remain separately identified reuse.

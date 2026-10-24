# ResourceStability offline packet

No live admission authority. Only immutable Git-object reads and local offline
Python are used. Do not execute any historical host/local runner. No SSH,
compiler, build, scope, consumer, key or RPC operation is authorized.

`ResourceStability_evaluator.evaluate(old,before,after,Q,phase=...,expected=...,
expected_unit=...)` consumes complete recorded or explicit synthetic snapshots.
Every synthetic input needs self_observation with pid/starttime/unified_path/path
and matching validated membership. Inside-scope also needs exact explicit unit.
The original scanner, observe and bind_scope are loaded unchanged from pinned
Git source; no old evaluate global is replaced. Public read_only_admission raises.

Source/policy assessment and exact before/after statements are in this job's
evidence directory. `ResourceStability-evaluator.diff` is reviewable against the
pinned old GO module. Dependencies are explicit in ResourceStability_sources.py.

The following commands have ALREADY run; do not repeat unchanged successful
checks. Each receipt records its exact interpreter command and source hashes:

    python3 -B tools/resource-stability-20261025/ResourceStability_receipt.py ResourceStability_tests.py focused-third
    python3 -B tools/resource-stability-20261025/ResourceStability_receipt.py ResourceStability_audit.py audit-third

The runner records/checks measured peak RSS <512 MiB; Darwin rejected lowering
RLIMIT_AS and RLIMIT_DATA. This is not an enforced OS address-space cap. Tests
are eight new focused groups; original unchanged suites are not run. Audit
replays the original v2 API under ordered captured I/O, reconstructs full original
input/report hashes without persisting >5 MB derived JSON, then applies the new
policy to the SAME snapshots counterfactually. Initial14866 inputs are reused
from the audited summary; their historical replay is not rerun. Failure logs
and receipts are retained. No historical runtime/pin recertification is claimed.

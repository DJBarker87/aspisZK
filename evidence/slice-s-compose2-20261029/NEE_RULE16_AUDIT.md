# Rule 16 resumption audit

Resume from lead WIP 393e863922. ATTEMPTS contains 40 Kani and 23 Lean scopes.
Authorized remainder: 15 Kani (40 minus 40 plus 15), 127 Lean. Historical
attempts and patches are immutable evidence; no failed attempt is erased.

Current validator output is 2/97 composed rows CLOSED (payment canonicality),
0/7 roots. The stage-3 12/97 statement is superseded: WIP shape admission checks
already reduced the accepted count to 2. Fixed4, common record, tuple and borrowed
shapes still need complete ruling-(t) admission. No root was ever CLOSED.

SUSPENDED: NEE_K024 pool_v1::pair_forest_accounts::NEE_loop_frame::step_frame;
NEE_K026 pool_v1::pair_tree_profile::NEE_loop_frame::step_frame. START/END were
written statics. Their controls K025/K027 do not rehabilitate them. K023 failed
before proof. K028 common_oracle timed out and has no credit; it also wrote
statics. K001..004 oracle_domain_positive never passed; still excluded.

Inherited NED_K034/K035 window_6 caller logs use written statics; their earlier
part-(1) credit is SUSPENDED regardless of the historical ruling-(y) statement.
All inherited NED call-window/binding log certificates with written statics are
suspended until audited/re-run. None is used to close a root in this packet.

NEE_K005..022 direct contract harnesses do not call the static-backed oracle:
frame_m31/common/parts invoke the actual pure target; payment_frames constructs
inputs and invokes its actual pure target and pure specification. No reachable
stub writes a static (only the pinned pure KMX copies). NEE_K029..040 shape
controls likewise contain no static, observer or function-pointer operation.
These static-free reachable cones retain local evidence; shape admission and
all other certificate gates still apply. Unreachable historical oracle source
in a compiled module is not used as a log. New generators remove it entirely.
Lean-only results remain valid development evidence; none proves a native root.

Runner change: own Kani budget guard increased from 40 to exactly 55 to account
for the explicit 15-run grant; source/graph/features/KMX/lock/caps checks remain.
Pure constructor imports now omit the entire obsolete writable-static oracle.
No shared infrastructure, shipped source, key or artifact changed.

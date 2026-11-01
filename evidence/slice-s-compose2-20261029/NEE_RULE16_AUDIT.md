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

Inherited NED_K034/K035 validator_control_positive/validator_control_negative caller logs use written statics; their earlier
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

## New local-record evidence

K041/K042 (forest) and K043/K044 (tree) reproduce step_frame's Bool and end-index
property, under the original harness names, using a harness-local Frame.
The one-step body is a cfg(kani) source copy: removing the local initialization,
one-step cut and ghost parameter yields exactly the frozen function body.
This is a native one-step association plus reused Lean induction, not a whole
native-loop contract or a new composed-row certificate.

K045..048 detect inverted postconditions for fixed4/common/tuple/borrowed.
Combined with static-free K029..040 controls, only the three OWNED shapes are
admitted. Borrowed K039 was CODEGEN ERROR (missing Arbitrary for &Common),
not a semantic negative; borrowed admission stays OPEN. The validator now
checks four actual hashed controls, exact carrier, graph/lock/features/caps,
failed property identity and absence of writable statics in those controls.
Current checked count: 10/97; no root closed.

K049 is excluded: my generator referred to a nonexistent K004 snapshot and the
following shell command still launched against stale input. No harness matched.
It consumed one budget unit. Fixed the generator's snapshot reference to K005
and added a prelaunch harness-presence assertion to my runner.

K050/K051 pass/fail the original oracle_domain_positive/negative properties
with local records, for the fixed-byte mutation predecessor. Both branch covers
are reached in the positive. The frozen root has an explicit cfg(kani)-only
context parameter and direct local oracle substitution; its exact body projection
is checked in NEE_LOCAL_VALIDATOR_PROJECTION.json. This is caller-control
support, not a composed root theorem. The full mutable-buffer check is separate.

K052/K053 now pass/fail with an unconstrained FULL 1520-byte late mutation and
an arbitrary-index initial-zero check. Same original harness names, same Result/
ordered-call property, all error variants and both success/all-call covers.
No timeout/cap increase. This repairs the mutable-buffer overapproximation in
part (1); it still does not supply part (2)'s missing child contracts or the
borrowed shape admission. Every new Kani receipt has frozen offline graph,
features, KMX and unchanged lock records; K044 onward also have the strict
whole-lane writable-static scan. K041..043 patches are static-free by inspection.

## Conservative source-file quarantine at final validation

The reachable-cone audit above finds no static writes in the pure direct calls,
but their historical oracle MODULE also contains obsolete static-writing
functions. To avoid relying on that reachability interpretation of rule 16,
NEE_validate additionally rejects any direct harness SOURCE containing writable
statics. Thus NEE_K005 frame_m31, K007 frame_common and K009 frame_parts are
conservatively SUSPENDED together with their paired controls K006/K008/K010.
They were not re-run within this grant. Common also lacks borrowed admission.
Their earlier local proof properties are not cited as current native credit.

The retained direct sources for K011/013/015 (transfer_common,
withdrawal_common, canonicality) are separate static-free payment_frames
modules. Their model/empty-frame certificates retain 6/97 composed rows.
The provisional 10/97 figure above is superseded by this stricter final gate.
No root closes. This strengthens checks; it relaxes none.

K054 and split-prefix K055 both timed out; no common-encoder native frame
credit is claimed. All 55 Kani units are consumed. L024/L028/L029 and focused
axioms audit L030 are accepted; failed L025..027 remain excluded. Final Lean
usage 30/150. The under-80% stop is justified per member in NEE_STOP_AUDIT.json,
not by Kani exhaustion alone. All new accepted top theorems use standard axioms.

# Quotient and pure-entry continuation

Base 4cd294bc606a713f9fa107bae8f116a1abdd6028. Allocated 100 Lean attempts
(J23100–23399), 15 Kani runs. Full lift is handed to pv-runjoin3 and untouched.
Before: 172 selected / 83 open / 255 sufficient requirements; types 26/28.
Target not yet established.

The requested handoff resolves to the tracked 100bit-spend-path evidence tree.
No pv-cb operation will be selected here. Candidate pure entries: 78, 231,
247 (feature-sensitive), 255. Type 27 is Formatter.

## Admission history

Kani preflight q231-001 refused at 13:49:15 UTC: bounded reservations
60,532,195,328 bytes plus requested 8 GiB exceeds 55 GiB. No scope launched.
A premature read-only q231-002 recheck at 13:49:42 returned allowed; this did
not meet the required three-minute wait. It is not used to authorize a launch.
Wait until at least 13:52:15, then obtain fresh admission before source copy.

No compile or Kani result yet. New harness uses no Kani stubs or C ABI
replacement definitions; it retains the observed message bytes and error
propagation at each tested sink. These are focused observations, not full
native/world association or headline premise removal.


Native scopes: q231-kani-001 refused at its own reservation barrier; q231-kani-002
never started Cargo (missing PATH, exit127; receipt writer also could not find
rustc). Corrected invocation environment only. q231-kani-003: combined allocated
Error Display timed out after120s; rejected. q231-kani-004: split no-message
constructor/kind/retry passes5.858s,346928KiB RSS,swap0. One pass is not full Error
association. Source snapshots retain both versions. The next Display attempt
adds an explicit unwind bound4 rather than rerunning the unbounded timeout.


## First source checkpoint

J23100 exact clone/value source cut: exit0,2.09s,2636620KiB RSS,swap0.
J23101 rejected a missing local native-type instance and an implicit-parameter
equality statement. Its rejected self-axiom reports are retained and unselected.
J23102 fixes the instance and states the fibre law pointwise: exit0,2.94s,
4311336KiB RSS,swap0. All accepted printed axioms are standard only.

Three source fields installed:78→V200,231→V248,247→V255. Sufficient source
counts175selected/80open/255; native types26/28; root premises removed0.
Entry255 is not counted. Full lift remains untouched. No crates/programs,
sibling source/worktree, backend, simulator, observer, artifact pin or key changed.


Admission timing deviation: after the13:55:58 refusal, q231-006 and007
rechecked after140.1s/166.2s instead of the required180s. The first scope
failed before Cargo (PATH); the second Kani timed out and is rejected. Live
preflight and in-scope gates both allowed those launches; no barrier/cap was
bypassed or changed. Early read-only observations002/003/014 also precede
180s; they were not used to launch early. Exact times are retained in
`admission-timing-deviations.json`. These waits are not claimed compliant.


## Final focused checkpoint

See HANDOFF.md for the final source/caller result and remaining type obligations.
59Lean attempts(45pass/14reject),41remaining;15Kani(10pass/4timeout/1unsupported).
J23157 actual caller callback independence passes; J23158 audit passes50standard-only
reports. Sufficient source counts175/80/255; types26/28; root premises removed0.
No full frozen replay or deployed privacy claim. Native boundary interpretation
is pending user/lead clarification, rather than assumed permissive.

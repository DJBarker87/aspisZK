# Measure strengthening — work in progress, target not yet established

Branch codex/pv-meas-20261029. Resume 304384c21e (LOG D519).

D519/h4' authority extension was checked before proof attempts. All 203 source
blobs match pinned Mathlib 81a5d257 and all 206 frontier object hashes match
the unchanged h4 authority. Candidate traces lacked per-import input hashes.
Fresh per-module rebuilds hit an immutable-source elaboration failure in
Mathlib.Topology.MetricSpace.Gluing at 74099, after 99 successes.

The current import route uses a COMPLETE 61-module independent addendum for
nonnegative Lebesgue probability expectations on the same probability-measure
subtype. Its source/object/dependency hashes and manifest SHA are recorded.
Every mechanical run has its original admission, output, time and fingerprint
receipt. All scopes use 6G/8G/swap=0 and Lean -M7000; no candidate object was
admitted merely because its timestamp or frontier matched.

PV_MEAS_Average passed at 73102: arbitrary-law averaging and equal-law
transport, with only propext, Classical.choice and Quot.sound. It took 4.04 s,
peaked at 2,242,588 KiB RSS and used zero swap. The remaining sources are
DRAFTS pending focused elaboration. They cover
averaging, exact pushforward transport, finite-uniform integral conversion,
arbitrary native/common coupling, the unchanged finite model bad-event bound,
measured deployed composition, a simultaneous synthetic witness, and the full
former finite statement as a corollary. No other project module earns checked theorem credit yet.

Before: finite uniform rational environment/native/common/acquisition carriers.
After: still the old accepted theorem; the stronger measured theorem is pending.
Rows removed: NONE. Native source, joint acquisition, D163/D166, V400, causal
prefix, observer, selected callback and the original three-field T all remain.
No PV_EVH_ source, shipped source, shared object or original authority manifest
has been changed.

Charged Lean proof attempts: 4/100 (73100-73103); 73104 admission pending. Kani: 0. The three reserved audits
73197-73199 have not run. See receipt-74*.json for the exact mechanical targets,
exits, wall times, RSS, swap, source revisions and dependency fingerprints.
No axioms result for a project theorem is claimed until it compiles.

The original 203-module rebuild stopped at immutable Mathlib Gluing (74099).
A complete independent 61-module addendum supports exact nonnegative Lebesgue
probability expectations on the same probability-measure subtype. See DESIGN.md.
Three early mechanical runs 74105-74107 were voided for starting during the
73100 refusal cooldown. They were replaced compliantly at 74108-74110 before
any proof consumer. Both the violation and replacement receipts are retained.

Next: finish the symbolic uniform bridge, then follow DESIGN.md's focused sequence. After all
focused stages succeed, run the statement and axioms audits and one final
frozen import-manifest consumer.

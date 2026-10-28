# Import-only correction after the first source failure

51322 stopped at R1Z.PV_RunJoin_WithdrawalIdentification16 after23 accepted
modules. The missing names are PV_Src_CanonicalRoots.table and
PV_Src_RootHelper.source. The original source imports RecordsAdapter16 and
FixtureArguments but not the helper that supplies those declarations.

The selected RootHelper source already defines source, and imports the selected
CanonicalRoots transitively. Neither dependency is an EJR/tracked conflict:
both resolve under h5 at the same committed paths/hashes already in the plan.
No dependency variant was switched. Commit364a4b6fb8 adds only the explicit
`import R1Z.PV_Src_RootHelper` to the h5-resolved identification module, leaving
its theorem statement and proof unchanged. This is the trivial import fix
expressly permitted by local-lean.txt rule1 (new modules only except trivial
import/name fixes).

The original failed source and full original compiler/time logs are retained
as51322-*; its compiler-produced sorryAx is rejected and receives no credit.
The old source SHA is6798275aea402f83d2a7b16411a6da816802847e65aadbedd479a4de656bd0bb.
The new committed blob/hash/revision are in build-plan.json's import_fix and
module pin. Historical focused-resolution.json and initial source snapshots
retain their original meaning; this addendum and updated build-plan supersede
that ONE h5 source pin for subsequent compilation.

Uncompiled modules are rescheduled in topological order, first satisfying the
new explicit helper dependency. The changed identification module is isolated
as a singleton attempt. Every already accepted fresh object is retained and
excluded from the new queue; there is no unchanged failed resubmission and no
unchanged successful dependency replay. Caps and source authority order stay
unchanged. The original build plan is retained as build-plan-before-import-fix.json.

The isolated changed-source replacement passed as51327: exit0, scope wall1.95s (module wall1.91s),
RSS4362846208bytes,swap0,standard axioms. The original51322 failure is
superseded for this module, not deleted or relabelled as a pass.

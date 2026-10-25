# Hir stage 4: deterministic selected-pair experiment

Target not yet established. Zero global ledger rows removed.

Hir_SelectedExecution.selected shows that the pure deterministic scan over the
recorded reached calls finds an actual successful writer for accepted TX2.
The scan has no H input. Hir_LifetimeExperiment.program executes the scheduler
ONCE and the submitted TX2 ONCE; it selects TX1 from already recorded native
replies. Hir_RecordErasure preserves all-world ordered logs and outputs exactly.

Hir_SelectedVersion.on_cuts derives the selected pair's actual post-copy version
history for any same-pair cuts; Hir_Authenticated.on_cuts derives complete input
identity from that history and P2Prime. Hir_AcceptedInputs.accepted discharges
both history and P2Prime in this lifetime family, with the common bad-event
alternative. Hir_AcceptedDriver.accepted connects that SAME source pair to the
installed first-constants driver and source-indexed canonical Carried input.
It does not require SessionA preparation or arithmetic owner laws for this local
acceptance result. Existing extraction/SDK/copy/runtime trust stays explicit.

Hir_LifetimeJoint.one_loss checks exactly ONE charge
6*(Q0+Q1+2965)^2/2^256. The scheduler budget covers ALL intervening calls and
adversary queries, canonical replay1040 and four complete account-byte reads
are added in the same log. No second history/canonical charge or independence
is used. Selection and recording ask no extra question. The conservative1921
source envelope is retained even though the selected writer is not replayed.

The source family still uses the explicit partial-syscall experiment and a
genesis/owner-assignment-admissible runtime schedule. No proof yet identifies
this with the complete deployed Pool/lifetime experiment. There is no
Hir_Top.deployed closure or global recount removal. L159 is untouched.

Hir_KANI004 checks the actual full Pool checkpoint encoder (all fields arbitrary)
and BOTH actual borrowed freshness guards: every successfully encoded192-byte
checkpoint has its nonzero A marker and is rejected by both reinitialization
checks, unchanged.864 checks,0 failures;53.17715s,1587452KiB,swap0,optimized.
This strengthens the local native lifecycle helpers; it does not enumerate all
Pool dispatch routes, aliases, CPI authorities or source-to-ELF correspondence.

Budget67/100 Lean submissions,4/30 Kani;1 Charon,1 failed Aeneas. All current
new modules match passing exact-source receipts. All accepted audits standard
axioms only. No timeout/memory kill, source adoption, package replay or cap
increase. Repository shipped files and other worker sources are unchanged.

import Hir_CutBindingTransport
import T2R_Top
set_option autoImplicit false
set_option pp.proofs false

-- BEFORE and actual AFTER: the actual root is unchanged. No Hir_Top.deployed
-- exists, so no global premise-removal credit is claimed by this packet.
#print AspisR1.T2R_Top.deployed
#print AspisR1.T2R_Acceptance.Facts
#print AspisR1.T2R_CallerSource.Outcome
#print AspisR1.S2W_NativeConsolidation.SourceCuts

-- New constructed source family: different runtime/scheduler quantifiers,
-- with source-derived writer/history, one charged event, no new trust adoption.
#print AspisR1.Hir_SelectedDriver.accepted
#print AspisR1.Hir_SelectedJoint.one_loss
#print AspisR1.Hir_SelectedBudget.source
#print AspisR1.Hir_CutBindingTransport.same_pair
#print AspisR1.Hir_IdealLifetime.total_instance
#print AspisR1.Hir_SyscallStatusGap.status_gap
#print AspisR1.Hir_ExactMargin.event_margin

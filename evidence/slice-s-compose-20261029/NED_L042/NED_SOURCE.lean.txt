import NDM_CohortCommon
import NDM_CommonWindows
set_option autoImplicit false
namespace NEC_Common
open Aeneas Aeneas.Std Result
open AdapterRw
open AspisR1.JHf_Carrier
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
abbrev Candidate := NDM_CommonCarrier.Candidate
abbrev Common := NDM_CommonCarrier.Common

/-- No numerical or canonicality restriction: every typed record is admitted.
Native allocation and physical interpretation are separate trust boundaries. -/
def PacketDomain (_a : Auth) (_c : Candidate) : Prop := True

theorem caller_domain (a : Auth) (c : Candidate) : PacketDomain a c := True.intro

/-- The safe extracted reference, SAME coherent adopted constructor and exact
record assembly. The native windows are still supplied by the native packet. -/
theorem reference_cohort (a : Auth) (c : Candidate) :
 (do let raw ← AspisR1AdapterReconstruct.r1_pool_adapter.asq8_common
      (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c)
     ok (NDM_CommonCarrier.project (fromPoolV1PairForestTerminalCommonV1 raw))) =
 NDM_Reference.common_ref a.master_account a.checkpoint_account a.selected_lane_account
 a.selected_lane.lane_id a.checkpoint.checkpoint_sequence a.checkpoint.global_root
 a.live_snapshot c := NDM_CohortCommon.cohort a c

theorem windows_transport (a : Auth) (c : Candidate) (actual : Common)
 (windows : NDM_CommonWindows.Fields actual (NDM_CommonCarrier.value a c)) :
 actual = NDM_CommonCarrier.value a c ∧
 AspisR1AdapterReconstruct.r1_pool_adapter.asq8_common
  (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c) =
 ok (toPoolV1PairForestTerminalCommonV1 actual) := by
 have h := NDM_CommonWindows.assemble _ _ windows
 subst actual
 exact ⟨rfl,NDM_CohortCommon.emitted a c⟩

#print axioms caller_domain
#print axioms reference_cohort
#print axioms windows_transport
end NEC_Common

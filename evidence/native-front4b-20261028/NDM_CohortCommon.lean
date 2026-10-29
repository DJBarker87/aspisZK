import NDM_CommonCarrier
import JHf_Carrier14
set_option autoImplicit false
namespace NDM_CohortCommon
open Aeneas Aeneas.Std Result
open AspisR1.JHf_Carrier

theorem emitted (a : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
 (c : NDM_CommonCarrier.Candidate) :
 AspisR1AdapterReconstruct.r1_pool_adapter.asq8_common
  (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c)=
 ok (toPoolV1PairForestTerminalCommonV1 (NDM_CommonCarrier.value a c)) := rfl

/-- Association is to the actual emitted common constructor consumed by op52,
 not a standalone free cohort slot. Native Box transport remains OPEN. -/
theorem cohort (a : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
 (c : NDM_CommonCarrier.Candidate) :
 (do let raw ← AspisR1AdapterReconstruct.r1_pool_adapter.asq8_common
       (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c)
     ok (NDM_CommonCarrier.project (fromPoolV1PairForestTerminalCommonV1 raw)))=
 NDM_Reference.common_ref a.master_account a.checkpoint_account a.selected_lane_account
 a.selected_lane.lane_id a.checkpoint.checkpoint_sequence a.checkpoint.global_root
 a.live_snapshot c := by
 rw [emitted]
 rfl

#print axioms emitted
#print axioms cohort
end NDM_CohortCommon

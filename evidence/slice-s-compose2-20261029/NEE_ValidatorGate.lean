import NEE_RawValidatorPrefix
set_option autoImplicit false
noncomputable section
namespace NEE_ValidatorGate
open Aeneas Aeneas.Std Result AspisR1AdapterReconstruct
open NBN_StatementResult NED_ErrorCarriers
attribute [local instance] Classical.propDecidable

def normalized (c : NED_ReconstructCarriers.Common) (next : NEE_RawValidatorPrefix.R) : NEE_RawValidatorPrefix.R :=
  if c.master_account = zero ∨ c.checkpoint_account = zero ∨ c.selected_lane_account = zero
  then ok (.Err .NonZeroBinding)
  else if 8 ≤ c.output_lane.val then ok (.Err .InvalidOutputLane) else next

/-- Prefix transport is independent of every child computation. -/
theorem result (c : NED_ReconstructCarriers.Common) (next : NEE_RawValidatorPrefix.R) :
    NEE_RawValidatorPrefix.gate (NED_ReconstructCarriers.toRawCommon c) next =
    normalized c next := by
  unfold NEE_RawValidatorPrefix.gate normalized
  simp only [NBH_ArrayEq.source,bind_tc_ok,NED_StatementCarrierFields.master,
    NED_StatementCarrierFields.checkpoint,NED_StatementCarrierFields.selected_lane,
    NED_StatementCarrierFields.lane,decide_eq_true_eq]
  have cast : core.convert.num.FromUsizeU8.from c.output_lane =
      Usize.ofNatCore c.output_lane.val (by scalar_tac) := by scalar_tac
  simp only [cast,lift,bind_tc_ok,
    aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT]
  by_cases hm : c.master_account = zero
  · simp only [zero] at hm
    simp only [hm,decide_true,if_true,true_or]
  · by_cases hc : c.checkpoint_account = zero
    · simp only [zero] at hm hc
      simp only [hm,hc,decide_false,decide_true,if_false,if_true,false_or,true_or]
    · by_cases hs : c.selected_lane_account = zero
      · simp only [zero] at hm hc hs
        simp only [hm,hc,hs,decide_false,decide_true,if_false,if_true,false_or]
      · by_cases lane : 8 ≤ c.output_lane.val
        · have large : (Usize.ofNatCore c.output_lane.val (by scalar_tac)) ≥ 8#usize := by scalar_tac
          simp only [zero] at hm hc hs
          simp only [hm,hc,hs,decide_false,if_false,false_or,lane,large,if_true]
        · have small : ¬ (Usize.ofNatCore c.output_lane.val (by scalar_tac)) ≥ 8#usize := by scalar_tac
          simp only [zero] at hm hc hs
          simp only [hm,hc,hs,decide_false,if_false,false_or,lane,small]

#print axioms result
end NEE_ValidatorGate

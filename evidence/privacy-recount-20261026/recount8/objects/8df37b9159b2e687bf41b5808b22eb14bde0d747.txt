import R1Z.PV_RDB2C_PV_B2_C_Powers7Total
import R1Z.PV_RDB2C_PV_B2_C_MaterializeWrapper
set_option autoImplicit false
namespace PV_B2_C_MaterializeCompose
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
/-- Complete success for every initial caller array once the remaining per-cell
proof is supplied. Powers and loop termination are discharged here. This local
hypothesis remains a P obligation, not a privacy trust item. -/
theorem source (w : host_weights.Weights) (kappa : E) (out : Out)
    (hc : ∀ k : Powers, host_weights.powers7 kappa = ok k →
      PV_B2_C_MutationTotal.CellsTotal w k) :
    ∃ updated, pv_b2_materialize w kappa out = ok (core.result.Result.Ok (),updated) := by
  obtain ⟨k,hk⟩ := PV_B2_C_Powers7Total.source kappa
  exact PV_B2_C_MaterializeWrapper.total w kappa out k hk (hc k hk)
#print axioms source
end PV_B2_C_MaterializeCompose

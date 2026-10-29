import PV_B3P_RangeFold13227
import PV_B3P_RoundQPackedLink13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227
set_option autoImplicit false
/-- Explicit forward Range source loop; no whole-body arithmetic reduction. -/
def source_round_range13_QPacked (state : RoundState10) (constants1 : Array aspis_core.field.QM31 16#usize) := do
  let state1 ← range_loop13 (round_q_step10 constants1) 0#usize 16#usize state
  reference_poseidon.external_linear_packed state1

theorem range_round_model13_QPacked (state : RoundState10) (constants1 : Array aspis_core.field.QM31 16#usize) :
    source_round_range13_QPacked state constants1 = source_round13_QPacked state constants1 := by
  unfold source_round_range13_QPacked source_round13_QPacked
  rw [range_sixteen13]

theorem range_round_link13_QPacked :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_full_round_packed source_round_range13_QPacked :=
  (funext fun state => funext fun constants1 => range_round_model13_QPacked state constants1).trans round_link13_QPacked
#print axioms range_round_model13_QPacked
#print axioms range_round_link13_QPacked
end PV_B3P_Binding13227

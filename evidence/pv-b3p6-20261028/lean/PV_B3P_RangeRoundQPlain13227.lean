import PV_B3P_RangeFold13227
import PV_B3P_RoundQPlainLink13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227
set_option autoImplicit false
/-- Explicit forward Range source loop; no whole-body arithmetic reduction. -/
def source_round_range13_QPlain (state : RoundState10) (constants1 : Array aspis_core.field.QM31 16#usize) := do
  let state1 ← range_loop13 (round_q_step10 constants1) 0#usize 16#usize state
  reference_poseidon.external_linear_lazy state1

theorem range_round_model13_QPlain (state : RoundState10) (constants1 : Array aspis_core.field.QM31 16#usize) :
    source_round_range13_QPlain state constants1 = source_round13_QPlain state constants1 := by
  unfold source_round_range13_QPlain source_round13_QPlain
  rw [range_sixteen13]

theorem range_round_link13_QPlain :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_full_round source_round_range13_QPlain :=
  (funext fun state => funext fun constants1 => range_round_model13_QPlain state constants1).trans round_link13_QPlain
#print axioms range_round_model13_QPlain
#print axioms range_round_link13_QPlain
end PV_B3P_Binding13227

import PV_B3P_RangeFold13227
import PV_B3P_RoundMPlainLink13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227
set_option autoImplicit false
/-- Explicit forward Range source loop; no whole-body arithmetic reduction. -/
def source_round_range13_MPlain (state : RoundState10) (constants1 : Array U32 16#usize) := do
  let state1 ← range_loop13 (round_m_step10 constants1) 0#usize 16#usize state
  reference_poseidon.external_linear_lazy state1

theorem range_round_model13_MPlain (state : RoundState10) (constants1 : Array U32 16#usize) :
    source_round_range13_MPlain state constants1 = source_round13_MPlain state constants1 := by
  unfold source_round_range13_MPlain source_round13_MPlain
  rw [range_sixteen13]

theorem range_round_link13_MPlain :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_full_round_m31_constants source_round_range13_MPlain :=
  (funext fun state => funext fun constants1 => range_round_model13_MPlain state constants1).trans round_link13_MPlain
#print axioms range_round_model13_MPlain
#print axioms range_round_link13_MPlain
end PV_B3P_Binding13227

import PV_B3P_Operations12227
import PV_B3P_RangeFold13227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227
set_option autoImplicit false

/-- The source range 0..16 runs in increasing order; its lane step preserves
both subfield and whole-element stores in the M31 case. The external layer
is called exactly once, after the range completes. -/
def native_round_MPlain15 (state : RoundState10) (constants1 : Array U32 16#usize) :
    Result (Array aspis_core.field.QM31 16#usize) := do
  let state1 ← range_loop13 (round_m_step10 constants1) 0#usize 16#usize state
  reference_poseidon.external_linear_lazy state1

theorem native_round_MPlain_binding15 (state : RoundState10)
    (constants1 : Array U32 16#usize) :
    native_round_MPlain15 state constants1 = reference_poseidon.full_round_m31_constants state constants1 := by
  unfold native_round_MPlain15
  rw [range_sixteen13]
  exact (full_round_m31_constants_source_fold11 state constants1).symm
#print axioms native_round_MPlain_binding15
end PV_B3P_Native15227

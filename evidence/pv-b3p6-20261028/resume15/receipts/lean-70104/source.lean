import PV_B3P_Operations12227
import PV_B3P_RangeFold13227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227
set_option autoImplicit false

def native_leading15 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    Result (Array aspis_core.field.QM31 4#usize) := do
  let state ← range_loop13 (leading_step12 openings.xor12_z) 0#usize 8#usize openings.z
  leading_finish12 state

theorem leading_indices15 : usize_indices11 8 0#usize =
    [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize] := by
  simp only [usize_indices11,next11_20_0,next11_20_1,next11_20_2,next11_20_3,
    next11_20_4,next11_20_5,next11_20_6,next11_20_7]

theorem native_leading_binding15
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    native_leading15 openings = reference_poseidon.leading_pair_packed openings := by
  unfold native_leading15
  rw [range_as_fold13 _ 0#usize 8#usize 8 _ (by rfl),leading_indices15]
  exact (leading_pair_packed_binding12 openings).symm
#print axioms leading_indices15
#print axioms native_leading_binding15
end PV_B3P_Native15227

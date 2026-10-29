import PV_B3P_InternalOutput1215227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false
def internal_output_tail12_14 (full_sum : InternalSum12) (state : InternalState12) : Result InternalState12 := do
  let q43 ← Array.index_usize state 14#usize
  let i13 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 13#usize
  let q44 ← reference_poseidon.internal_shift227 q43 full_sum i13
  let state15 ← Array.update state 14#usize q44
  let q45 ← Array.index_usize state15 15#usize
  let i14 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 14#usize
  let q46 ← reference_poseidon.internal_shift227 q45 full_sum i14
  Array.update state15 15#usize q46
attribute [local irreducible] Array.index_usize Array.update reference_poseidon.internal_sum227 reference_poseidon.internal_shift227 reference_poseidon.internal_full_sum227 reference_poseidon.internal_zero227 reference_poseidon.extension_limbs internal_output_step12 internal_output_tail12_15
theorem internal_output_cell12_14 (full_sum : InternalSum12) (state : InternalState12) :
    internal_output_tail12_14 full_sum state =
      (internal_output_step12 full_sum state 14#usize >>= internal_output_tail12_15 full_sum) := by
  have hsub : Usize.wrapping_sub 14#usize 1#usize = 13#usize := rfl
  unfold internal_output_tail12_14
  conv_rhs => simp only [internal_output_step12,hsub,lift,bind_tc_ok,PV_B3P_Ordered227.bind_assoc,bind_return12]
  apply bind_equal9
  intro x0
  apply bind_equal9
  intro x1
  apply bind_equal9
  intro x2
  apply bind_equal9
  intro next
  unfold internal_output_tail12_15
  rfl
theorem internal_output_fold12_14 (full_sum : InternalSum12) (state : InternalState12) :
    internal_output_tail12_14 full_sum state =
      PV_B3P_Ordered227.fold (internal_output_step12 full_sum) [14#usize, 15#usize] state := by
  rw [internal_output_cell12_14]
  simp only [PV_B3P_Ordered227.fold,bind_tc_ok,bind_return12]
  apply congrArg (fun finish => internal_output_step12 full_sum state 14#usize >>= finish)
  funext next
  simpa only [PV_B3P_Ordered227.fold,bind_tc_ok,bind_return12] using internal_output_fold12_15 full_sum next
#print axioms internal_output_cell12_14
#print axioms internal_output_fold12_14
end PV_B3P_Binding12227

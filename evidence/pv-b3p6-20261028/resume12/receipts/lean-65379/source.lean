import PV_B3P_InternalOutput1204227
import PV_B3P_IndexSteps9227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false
def internal_output_tail12_03 (full_sum : InternalSum12) (state : InternalState12) : Result InternalState12 := do
  let q21 ← Array.index_usize state 3#usize
  let i2 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 2#usize
  let q22 ← reference_poseidon.internal_shift227 q21 full_sum i2
  let state4 ← Array.update state 3#usize q22
  let q23 ← Array.index_usize state4 4#usize
  let i3 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 3#usize
  let q24 ← reference_poseidon.internal_shift227 q23 full_sum i3
  let state5 ← Array.update state4 4#usize q24
  let q25 ← Array.index_usize state5 5#usize
  let i4 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 4#usize
  let q26 ← reference_poseidon.internal_shift227 q25 full_sum i4
  let state6 ← Array.update state5 5#usize q26
  let q27 ← Array.index_usize state6 6#usize
  let i5 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 5#usize
  let q28 ← reference_poseidon.internal_shift227 q27 full_sum i5
  let state7 ← Array.update state6 6#usize q28
  let q29 ← Array.index_usize state7 7#usize
  let i6 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 6#usize
  let q30 ← reference_poseidon.internal_shift227 q29 full_sum i6
  let state8 ← Array.update state7 7#usize q30
  let q31 ← Array.index_usize state8 8#usize
  let i7 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 7#usize
  let q32 ← reference_poseidon.internal_shift227 q31 full_sum i7
  let state9 ← Array.update state8 8#usize q32
  let q33 ← Array.index_usize state9 9#usize
  let i8 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 8#usize
  let q34 ← reference_poseidon.internal_shift227 q33 full_sum i8
  let state10 ← Array.update state9 9#usize q34
  let q35 ← Array.index_usize state10 10#usize
  let i9 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 9#usize
  let q36 ← reference_poseidon.internal_shift227 q35 full_sum i9
  let state11 ← Array.update state10 10#usize q36
  let q37 ← Array.index_usize state11 11#usize
  let i10 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 10#usize
  let q38 ← reference_poseidon.internal_shift227 q37 full_sum i10
  let state12 ← Array.update state11 11#usize q38
  let q39 ← Array.index_usize state12 12#usize
  let i11 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 11#usize
  let q40 ← reference_poseidon.internal_shift227 q39 full_sum i11
  let state13 ← Array.update state12 12#usize q40
  let q41 ← Array.index_usize state13 13#usize
  let i12 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 12#usize
  let q42 ← reference_poseidon.internal_shift227 q41 full_sum i12
  let state14 ← Array.update state13 13#usize q42
  let q43 ← Array.index_usize state14 14#usize
  let i13 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 13#usize
  let q44 ← reference_poseidon.internal_shift227 q43 full_sum i13
  let state15 ← Array.update state14 14#usize q44
  let q45 ← Array.index_usize state15 15#usize
  let i14 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 14#usize
  let q46 ← reference_poseidon.internal_shift227 q45 full_sum i14
  Array.update state15 15#usize q46
attribute [local irreducible] Array.index_usize Array.update reference_poseidon.internal_sum227 reference_poseidon.internal_shift227 reference_poseidon.internal_full_sum227 reference_poseidon.internal_zero227 reference_poseidon.extension_limbs internal_output_step12 internal_output_tail12_04
theorem internal_output_cell12_03 (full_sum : InternalSum12) (state : InternalState12) :
    internal_output_tail12_03 full_sum state =
      (internal_output_step12 full_sum state 3#usize >>= internal_output_tail12_04 full_sum) := by
  have hsub : Usize.wrapping_sub 3#usize 1#usize = 2#usize := previous_exact _ _ rfl
  unfold internal_output_tail12_03
  conv_rhs => simp only [internal_output_step12,hsub,lift,bind_tc_ok,PV_B3P_Ordered227.bind_assoc,bind_return12]
  apply bind_equal9
  intro x0
  apply bind_equal9
  intro x1
  apply bind_equal9
  intro x2
  apply bind_equal9
  intro next
  unfold internal_output_tail12_04
  rfl
theorem internal_output_fold12_03 (full_sum : InternalSum12) (state : InternalState12) :
    internal_output_tail12_03 full_sum state =
      PV_B3P_Ordered227.fold (internal_output_step12 full_sum) [3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] state := by
  rw [internal_output_cell12_03]
  simp only [PV_B3P_Ordered227.fold,bind_tc_ok,bind_return12]
  apply congrArg (fun finish => internal_output_step12 full_sum state 3#usize >>= finish)
  funext next
  simpa only [PV_B3P_Ordered227.fold,bind_tc_ok,bind_return12] using internal_output_fold12_04 full_sum next
#print axioms internal_output_cell12_03
#print axioms internal_output_fold12_03
end PV_B3P_Binding12227

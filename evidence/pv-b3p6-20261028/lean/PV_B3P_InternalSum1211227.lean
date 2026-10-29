import PV_B3P_InternalSum1212227
import PV_B3P_IndexSteps9227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false
def internal_sum_tail12_11 (state : InternalState12) (old_zero : Array U32 4#usize) (part_sum : InternalSum12) : Result InternalState12 := do
  let q11 ← Array.index_usize state 11#usize
  let part_sum11 ← reference_poseidon.internal_sum227 part_sum q11
  let q12 ← Array.index_usize state 12#usize
  let part_sum12 ← reference_poseidon.internal_sum227 part_sum11 q12
  let q13 ← Array.index_usize state 13#usize
  let part_sum13 ← reference_poseidon.internal_sum227 part_sum12 q13
  let q14 ← Array.index_usize state 14#usize
  let part_sum14 ← reference_poseidon.internal_sum227 part_sum13 q14
  let q15 ← Array.index_usize state 15#usize
  let part_sum15 ← reference_poseidon.internal_sum227 part_sum14 q15
  let full_sum ← reference_poseidon.internal_full_sum227 part_sum15 old_zero
  let q16 ← reference_poseidon.internal_zero227 part_sum15 old_zero
  let state1 ← Array.update state 0#usize q16
  let q17 ← Array.index_usize state1 1#usize
  let i ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 0#usize
  let q18 ← reference_poseidon.internal_shift227 q17 full_sum i
  let state2 ← Array.update state1 1#usize q18
  let q19 ← Array.index_usize state2 2#usize
  let i1 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 1#usize
  let q20 ← reference_poseidon.internal_shift227 q19 full_sum i1
  let state3 ← Array.update state2 2#usize q20
  let q21 ← Array.index_usize state3 3#usize
  let i2 ←
    Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS 2#usize
  let q22 ← reference_poseidon.internal_shift227 q21 full_sum i2
  let state4 ← Array.update state3 3#usize q22
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
attribute [local irreducible] Array.index_usize Array.update reference_poseidon.internal_sum227 reference_poseidon.internal_shift227 reference_poseidon.internal_full_sum227 reference_poseidon.internal_zero227 reference_poseidon.extension_limbs internal_sum_step12 internal_finish12 internal_sum_tail12_12
theorem internal_sum_cell12_11 (state : InternalState12) (old_zero : Array U32 4#usize) (part_sum : InternalSum12) :
    internal_sum_tail12_11 state old_zero part_sum =
      (internal_sum_step12 state part_sum 11#usize >>= internal_sum_tail12_12 state old_zero) := by
  unfold internal_sum_tail12_11
  conv_rhs => simp only [internal_sum_step12,PV_B3P_Ordered227.bind_assoc]
  apply bind_equal9
  intro value
  apply bind_equal9
  intro next
  unfold internal_sum_tail12_12
  rfl
theorem internal_sum_fold12_11 (state : InternalState12) (old_zero : Array U32 4#usize) (part_sum : InternalSum12) :
    internal_sum_tail12_11 state old_zero part_sum =
      (PV_B3P_Ordered227.fold (internal_sum_step12 state) [11#usize, 12#usize, 13#usize, 14#usize, 15#usize] part_sum >>= internal_finish12 state old_zero) := by
  rw [internal_sum_cell12_11]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  apply congrArg (fun finish => internal_sum_step12 state part_sum 11#usize >>= finish)
  funext next
  simpa only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using internal_sum_fold12_12 state old_zero next
#print axioms internal_sum_cell12_11
#print axioms internal_sum_fold12_11
end PV_B3P_Binding12227

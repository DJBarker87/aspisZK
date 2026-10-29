import PV_B3P_InternalFinish12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false
def internal_sum_sequence12 (state : InternalState12) (part_sum : InternalSum12) : Result InternalSum12 := do
  let q1 ← Array.index_usize state 1#usize
  let part_sum1 ← reference_poseidon.internal_sum227 part_sum q1
  let q2 ← Array.index_usize state 2#usize
  let part_sum2 ← reference_poseidon.internal_sum227 part_sum1 q2
  let q3 ← Array.index_usize state 3#usize
  let part_sum3 ← reference_poseidon.internal_sum227 part_sum2 q3
  let q4 ← Array.index_usize state 4#usize
  let part_sum4 ← reference_poseidon.internal_sum227 part_sum3 q4
  let q5 ← Array.index_usize state 5#usize
  let part_sum5 ← reference_poseidon.internal_sum227 part_sum4 q5
  let q6 ← Array.index_usize state 6#usize
  let part_sum6 ← reference_poseidon.internal_sum227 part_sum5 q6
  let q7 ← Array.index_usize state 7#usize
  let part_sum7 ← reference_poseidon.internal_sum227 part_sum6 q7
  let q8 ← Array.index_usize state 8#usize
  let part_sum8 ← reference_poseidon.internal_sum227 part_sum7 q8
  let q9 ← Array.index_usize state 9#usize
  let part_sum9 ← reference_poseidon.internal_sum227 part_sum8 q9
  let q10 ← Array.index_usize state 10#usize
  let part_sum10 ← reference_poseidon.internal_sum227 part_sum9 q10
  let q11 ← Array.index_usize state 11#usize
  let part_sum11 ← reference_poseidon.internal_sum227 part_sum10 q11
  let q12 ← Array.index_usize state 12#usize
  let part_sum12 ← reference_poseidon.internal_sum227 part_sum11 q12
  let q13 ← Array.index_usize state 13#usize
  let part_sum13 ← reference_poseidon.internal_sum227 part_sum12 q13
  let q14 ← Array.index_usize state 14#usize
  let part_sum14 ← reference_poseidon.internal_sum227 part_sum13 q14
  let q15 ← Array.index_usize state 15#usize
  let part_sum15 ← reference_poseidon.internal_sum227 part_sum14 q15
  .ok part_sum15
attribute [local irreducible] Array.index_usize Array.update reference_poseidon.internal_sum227 reference_poseidon.extension_limbs reference_poseidon.internal_full_sum227 reference_poseidon.internal_zero227 reference_poseidon.internal_shift227
theorem internal_sum_sequence_fold12 (state : InternalState12) (part_sum : InternalSum12) :
    internal_sum_sequence12 state part_sum =
      PV_B3P_Ordered227.fold (internal_sum_step12 state) [1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] part_sum := by
  simp only [internal_sum_sequence12,PV_B3P_Ordered227.fold,internal_sum_step12,
    PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

def internal_entry_prefix12 (state : InternalState12) : Result InternalState12 := do
  let first ← Array.index_usize state 0#usize
  let old_zero ← reference_poseidon.extension_limbs first
  let part_sum ← internal_sum_sequence12 state (Array.repeat 4#usize 0#u64)
  internal_finish12 state old_zero part_sum

theorem internal_entry_factor12 (state : InternalState12) :
    reference_poseidon.internal_linear_lazy state = internal_entry_prefix12 state := by
  unfold reference_poseidon.internal_linear_lazy internal_entry_prefix12 internal_sum_sequence12
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  apply bind_equal9
  intro value_0
  apply bind_equal9
  intro value_1
  apply bind_equal9
  intro value_2
  apply bind_equal9
  intro value_3
  apply bind_equal9
  intro value_4
  apply bind_equal9
  intro value_5
  apply bind_equal9
  intro value_6
  apply bind_equal9
  intro value_7
  apply bind_equal9
  intro value_8
  apply bind_equal9
  intro value_9
  apply bind_equal9
  intro value_10
  apply bind_equal9
  intro value_11
  apply bind_equal9
  intro value_12
  apply bind_equal9
  intro value_13
  apply bind_equal9
  intro value_14
  apply bind_equal9
  intro value_15
  apply bind_equal9
  intro value_16
  apply bind_equal9
  intro value_17
  apply bind_equal9
  intro value_18
  apply bind_equal9
  intro value_19
  apply bind_equal9
  intro value_20
  apply bind_equal9
  intro value_21
  apply bind_equal9
  intro value_22
  apply bind_equal9
  intro value_23
  apply bind_equal9
  intro value_24
  apply bind_equal9
  intro value_25
  apply bind_equal9
  intro value_26
  apply bind_equal9
  intro value_27
  apply bind_equal9
  intro value_28
  apply bind_equal9
  intro value_29
  apply bind_equal9
  intro value_30
  apply bind_equal9
  intro value_31
  unfold internal_finish12 internal_output_tail12_01
  rfl
#print axioms internal_sum_sequence_fold12
#print axioms internal_entry_factor12
end PV_B3P_Binding12227

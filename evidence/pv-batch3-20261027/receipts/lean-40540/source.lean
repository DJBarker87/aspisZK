import PV_B3_ZeroArrays
namespace PV_B3_ZeroPolynomial
open Aeneas Aeneas.Std Result PV_B3_Copy_117 PV_B3_ZeroArithmetic PV_B3_ZeroArrays
set_option autoImplicit false
abbrev channels := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
abbrev triple := Array.repeat 3#usize Z
abbrev polynomial := Array.repeat 28#usize Z
theorem madd_zero : aspis_core.field.M31.add 0#u32 0#u32 = ok 0#u32 := by with_unfolding_all rfl
#print axioms madd_zero
-- Nine independent writes use generic constant-array restoration lemmas.
theorem accumulate : host_arithmetic.accumulate_channels channels Z Z = ok channels := by
  simp (disch := decide) only [host_arithmetic.accumulate_channels,
    aspis_core.field.QM31.ZERO,cadd_zero,madd_zero,triple_repeat,
    index_repeat,mutable_repeat,update_repeat,set_repeat,lift,bind_tc_ok]

theorem reconstruct_component : host_arithmetic.reconstruct_component (Array.repeat 3#usize 0#u64) = ok CZero := by
  with_unfolding_all rfl
#print axioms reconstruct_component

theorem reconstruct : host_arithmetic.reconstruct_channels channels = ok Z := by
  simp (disch := decide) only [host_arithmetic.reconstruct_channels,
    index_repeat,reconstruct_component,hostr_zero,cadd_zero,csub_zero,bind_tc_ok]
  rfl

theorem product3 : host_arithmetic.qm31_sum_products3 triple triple = ok Z := by
  simp (disch := decide) only [host_arithmetic.qm31_sum_products3,index_repeat,
    accumulate,reconstruct,bind_tc_ok]

theorem triple_eq : Array.make 3#usize [Z,Z,Z] = triple := rfl

#print axioms accumulate
#print axioms reconstruct
#print axioms product3
#print axioms triple_eq
theorem start0 : Usize.wrapping_mul 4#usize 0#usize = 0#usize := by scalar_tac
#print axioms start0
theorem offset0_1 : Usize.wrapping_add 0#usize 1#usize = 1#usize := by scalar_tac
#print axioms offset0_1
theorem offset0_2 : Usize.wrapping_add 0#usize 2#usize = 2#usize := by scalar_tac
#print axioms offset0_2
theorem offset0_3 : Usize.wrapping_add 0#usize 3#usize = 3#usize := by scalar_tac
#print axioms offset0_3
theorem start1 : Usize.wrapping_mul 4#usize 1#usize = 4#usize := by scalar_tac
#print axioms start1
theorem offset1_1 : Usize.wrapping_add 4#usize 1#usize = 5#usize := by scalar_tac
#print axioms offset1_1
theorem offset1_2 : Usize.wrapping_add 4#usize 2#usize = 6#usize := by scalar_tac
#print axioms offset1_2
theorem offset1_3 : Usize.wrapping_add 4#usize 3#usize = 7#usize := by scalar_tac
#print axioms offset1_3
theorem start2 : Usize.wrapping_mul 4#usize 2#usize = 8#usize := by scalar_tac
#print axioms start2
theorem offset2_1 : Usize.wrapping_add 8#usize 1#usize = 9#usize := by scalar_tac
#print axioms offset2_1
theorem offset2_2 : Usize.wrapping_add 8#usize 2#usize = 10#usize := by scalar_tac
#print axioms offset2_2
theorem offset2_3 : Usize.wrapping_add 8#usize 3#usize = 11#usize := by scalar_tac
#print axioms offset2_3
theorem start3 : Usize.wrapping_mul 4#usize 3#usize = 12#usize := by scalar_tac
#print axioms start3
theorem offset3_1 : Usize.wrapping_add 12#usize 1#usize = 13#usize := by scalar_tac
#print axioms offset3_1
theorem offset3_2 : Usize.wrapping_add 12#usize 2#usize = 14#usize := by scalar_tac
#print axioms offset3_2
theorem offset3_3 : Usize.wrapping_add 12#usize 3#usize = 15#usize := by scalar_tac
#print axioms offset3_3
theorem start4 : Usize.wrapping_mul 4#usize 4#usize = 16#usize := by scalar_tac
#print axioms start4
theorem offset4_1 : Usize.wrapping_add 16#usize 1#usize = 17#usize := by scalar_tac
#print axioms offset4_1
theorem offset4_2 : Usize.wrapping_add 16#usize 2#usize = 18#usize := by scalar_tac
#print axioms offset4_2
theorem offset4_3 : Usize.wrapping_add 16#usize 3#usize = 19#usize := by scalar_tac
#print axioms offset4_3
theorem start5 : Usize.wrapping_mul 4#usize 5#usize = 20#usize := by scalar_tac
#print axioms start5
theorem offset5_1 : Usize.wrapping_add 20#usize 1#usize = 21#usize := by scalar_tac
#print axioms offset5_1
theorem offset5_2 : Usize.wrapping_add 20#usize 2#usize = 22#usize := by scalar_tac
#print axioms offset5_2
theorem offset5_3 : Usize.wrapping_add 20#usize 3#usize = 23#usize := by scalar_tac
#print axioms offset5_3
theorem start6 : Usize.wrapping_mul 4#usize 6#usize = 24#usize := by scalar_tac
#print axioms start6
theorem offset6_1 : Usize.wrapping_add 24#usize 1#usize = 25#usize := by scalar_tac
#print axioms offset6_1
theorem offset6_2 : Usize.wrapping_add 24#usize 2#usize = 26#usize := by scalar_tac
#print axioms offset6_2
theorem offset6_3 : Usize.wrapping_add 24#usize 3#usize = 27#usize := by scalar_tac
#print axioms offset6_3
theorem block0 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 0#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    start0,offset0_1,offset0_2,offset0_3,lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block0
theorem block1 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 1#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    start1,offset1_1,offset1_2,offset1_3,lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block1
theorem block2 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 2#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    start2,offset2_1,offset2_2,offset2_3,lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block2
theorem block3 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 3#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    start3,offset3_1,offset3_2,offset3_3,lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block3
theorem block4 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 4#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    start4,offset4_1,offset4_2,offset4_3,lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block4
theorem block5 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 5#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    start5,offset5_1,offset5_2,offset5_3,lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block5
theorem block6 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 6#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    start6,offset6_1,offset6_2,offset6_3,lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block6
theorem block (i : Usize) (hi : i.val ≤ 6) :
    host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple i = ok Z := by
  have hc : i = 0#usize ∨ i = 1#usize ∨ i = 2#usize ∨ i = 3#usize ∨ i = 4#usize ∨ i = 5#usize ∨ i = 6#usize := by
    have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by omega
    rcases hv with h | h | h | h | h | h | h
    · exact Or.inl (UScalar.eq_of_val_eq h)
    · exact Or.inr (Or.inl (UScalar.eq_of_val_eq h))
    · exact Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (UScalar.eq_of_val_eq h))))))
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact block0 | exact block1 | exact block2 | exact block3 | exact block4 | exact block5 | exact block6
#print axioms block
end PV_B3_ZeroPolynomial

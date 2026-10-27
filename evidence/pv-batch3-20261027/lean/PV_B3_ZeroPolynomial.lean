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
theorem block0 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 0#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block0
theorem block1 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 1#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block1
theorem block2 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 2#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block2
theorem block3 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 3#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block3
theorem block4 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 4#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block4
theorem block5 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 5#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
#print axioms block5
theorem block6 : host_arithmetic.evaluate_state_only_polynomial.block_value polynomial triple 6#usize = ok Z := by
  simp (disch := decide) only [host_arithmetic.evaluate_state_only_polynomial.block_value,
    lift,index_repeat,triple_eq,product3,PV_B3_ZeroArithmetic.add,bind_tc_ok]
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

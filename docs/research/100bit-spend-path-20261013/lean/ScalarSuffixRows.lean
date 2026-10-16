import SameBoxedRowExact
import SelectorValueLaneGeneratedSlice
import ExtractedMaskReducerOps

/-! Checked source index arithmetic for the four asset/withdrawal rows. -/
set_option autoImplicit false
namespace AspisR1.ScalarSuffixRows
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReducerOps

private theorem small_bound (n : Nat) (hn : n < 2048) :
    n < 2 ^ UScalarTy.Usize.numBits := by
  rw [UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
  have hmax := Usize.cMax_bound_concrete.1
  omega

private theorem mul_exact (a b c : Usize) (hc : c.val < 2048)
    (h : a.val * b.val = c.val) : UScalar.mul a b = .ok c := by
  obtain ⟨q, hrun, hval⟩ := tryMk_success (ty := .Usize) (a.val * b.val)
    (by rw [h]; exact small_bound c.val hc)
  have hq : q = c := UScalar.eq_of_val_eq (hval.trans h)
  simpa only [UScalar.mul, hq] using hrun

private theorem add_exact (a b c : Usize) (hc : c.val < 2048)
    (h : a.val + b.val = c.val) : UScalar.add a b = .ok c := by
  obtain ⟨q, hrun, hval⟩ := tryMk_success (ty := .Usize) (a.val + b.val)
    (by rw [h]; exact small_bound c.val hc)
  have hq : q = c := UScalar.eq_of_val_eq (hval.trans h)
  simpa only [UScalar.add, hq] using hrun

theorem mul_two_sixteen : UScalar.mul 2#usize 16#usize = .ok 32#usize :=
  mul_exact _ _ _ (by scalar_tac) (by scalar_tac)
theorem add_twelve_32 : UScalar.add 32#usize 12#usize = .ok 44#usize :=
  add_exact _ _ _ (by scalar_tac) (by scalar_tac)
theorem mul_31_sixteen : UScalar.mul 31#usize 16#usize = .ok 496#usize :=
  mul_exact _ _ _ (by scalar_tac) (by scalar_tac)
theorem add_twelve_496 : UScalar.add 496#usize 12#usize = .ok 508#usize :=
  add_exact _ _ _ (by scalar_tac) (by scalar_tac)
theorem mul_28_sixteen : UScalar.mul 28#usize 16#usize = .ok 448#usize :=
  mul_exact _ _ _ (by scalar_tac) (by scalar_tac)
theorem add_twelve_448 : UScalar.add 448#usize 12#usize = .ok 460#usize :=
  add_exact _ _ _ (by scalar_tac) (by scalar_tac)
theorem mul_value_aux :
    UScalar.mul 16#usize pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK = .ok 1008#usize := by
  rw [pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK.eq_def]
  exact mul_exact _ _ _ (by scalar_tac) (by scalar_tac)
theorem add_two_1008 : UScalar.add 1008#usize 2#usize = .ok 1010#usize :=
  add_exact _ _ _ (by scalar_tac) (by scalar_tac)

#print axioms mul_two_sixteen
#print axioms add_twelve_32
#print axioms mul_31_sixteen
#print axioms add_twelve_496
#print axioms mul_28_sixteen
#print axioms add_twelve_448
#print axioms mul_value_aux
#print axioms add_two_1008
end AspisR1.ScalarSuffixRows

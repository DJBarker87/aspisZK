import NNU_MerkleChildren
set_option autoImplicit false
namespace AspisR1.NNY_BatchArithmetic
open Aeneas Aeneas.Std Result

theorem mul_zero : Usize.wrapping_mul 3#usize 0#usize=0#usize := by
 apply UScalar.eq_of_val_eq
 exact Port3_Wrapping.wrap_mul_value 3#usize 0#usize (by decide)
theorem mul_one : Usize.wrapping_mul 3#usize 1#usize=3#usize := by
 apply UScalar.eq_of_val_eq
 exact Port3_Wrapping.wrap_mul_value 3#usize 1#usize (by decide)
theorem sub_zero (n : Usize) : Usize.wrapping_sub n 0#usize=n := by
 apply UScalar.eq_of_val_eq
 rw [Usize.wrapping_sub_val_eq]
 change (n.val+(UScalar.size .Usize-0))%UScalar.size .Usize=n.val
 rw [Nat.sub_zero,Nat.add_mod_right,Nat.mod_eq_of_lt]
 rw [UScalar.size_def]
 exact n.bv.isLt
theorem sub_twelve : Usize.wrapping_sub 22#usize 10#usize=12#usize := by
 have cap : 22 < UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 apply UScalar.eq_of_val_eq
 rw [Usize.wrapping_sub_val_eq]
 change (22+(UScalar.size .Usize-10))%UScalar.size .Usize=12
 rw [show 22+(UScalar.size .Usize-10)=12+UScalar.size .Usize by omega,
  Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
#print axioms mul_zero
#print axioms mul_one
#print axioms sub_zero
#print axioms sub_twelve
end AspisR1.NNY_BatchArithmetic

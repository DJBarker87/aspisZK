import FIo_ReduceBounds
import FIo_NativeFuns
import LPe_MersenneReduction
set_option autoImplicit false
namespace AspisR1.LPf_ReductionWord
open Aeneas Aeneas.Std Result

/-- The native word fold has the natural value used in LPe's reduction theorem. -/
theorem fold_value (x : U64) :
    (FIo_ReduceBounds.fold x).val = LPe_MersenneReduction.fold x.val :=
by
  unfold FIo_ReduceBounds.fold U64.wrapping_add
  rw [UScalar.wrapping_add_val_eq, Nat.mod_eq_of_lt (FIo_ReduceBounds.sum_bound x)]
  have low : (x &&& 2147483647#u64).val = x.val % 2147483648 := by
    change (x.bv &&& (2147483647 : BitVec 64)).toNat = x.val % 2147483648
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.val 31
  rw [low, FIo_ReduceBounds.shr_val]
  rfl

theorem twice_value (x : U64) :
    (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)).val =
      LPe_MersenneReduction.fold (LPe_MersenneReduction.fold x.val) := by
  rw [fold_value, fold_value]

/-- Exact value of the actual extracted private reducer, including word casts
and wrapping subtraction. No successful output observation is a premise. -/
theorem native_reduce (x : U64) : ∃ z,
    FIo_Native.fast_pairing.canonical.reduce x = ok z ∧
    z.val = x.val % 2147483647 ∧ z.val < 2147483647 := by
  have hx : x.val < 18446744073709551616 := by scalar_tac
  have small : (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)).val < 4294967294 := by
    rw [twice_value]
    exact LPe_MersenneReduction.fold_twice_lt x.val hx
  have value := twice_value x
  have residue := LPe_MersenneReduction.reduce_eq_mod x.val hx
  unfold FIo_Native.fast_pairing.canonical.reduce
  simp only [FIo_Native.fast_pairing.canonical.P, lift, bind_tc_ok]
  change ∃ z, (if FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x) ≥ 2147483647#u64
    then ok (UScalar.cast .U32 (U64.wrapping_sub
      (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)) 2147483647#u64))
    else ok (UScalar.cast .U32 (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)))) = ok z ∧ _
  split
  · rename_i h
    have lower : 2147483647 ≤ (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)).val := by scalar_tac
    refine ⟨_, rfl, ?_, ?_⟩
    · unfold U64.wrapping_sub
      rw [UScalar.cast_val_eq, UScalar.wrapping_sub_val_eq]
      norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits,U32.size,U32.numBits]
      unfold LPe_MersenneReduction.reduce at residue
      rw [if_pos (by omega)] at residue
      omega
    · unfold U64.wrapping_sub
      rw [UScalar.cast_val_eq, UScalar.wrapping_sub_val_eq]
      norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits,U32.size,U32.numBits]
      omega
  · rename_i h
    have lower : (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)).val < 2147483647 := by scalar_tac
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [UScalar.cast_val_eq]
      norm_num [UScalar.size,UScalarTy.numBits,U32.size,U32.numBits]
      unfold LPe_MersenneReduction.reduce at residue
      rw [if_neg (by omega)] at residue
      omega
    · scalar_tac

#print axioms fold_value
#print axioms twice_value
#print axioms native_reduce
end AspisR1.LPf_ReductionWord

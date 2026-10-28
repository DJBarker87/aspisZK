-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_LPf_ReductionWord
set_option autoImplicit false
namespace AspisR1.LPf_CoreReduction
open Aeneas Aeneas.Std Result

/-- The two frozen source reducers place the u32 cast on opposite sides of
subtraction. Their twice-folded bounds make those placements equivalent. -/
theorem same (x : U64) :
    FIo_Native.aspis_core.field.reduce_u64 x =
    FIo_Native.fast_pairing.canonical.reduce x := by
  let m := FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)
  have small : m.val < 4294967294 := by
    rw [LPf_ReductionWord.twice_value]
    apply LPe_MersenneReduction.fold_twice_lt
    scalar_tac
  have cv : (UScalar.cast .U32 m).val = m.val := by scalar_tac
  unfold FIo_Native.aspis_core.field.reduce_u64 FIo_Native.fast_pairing.canonical.reduce
  simp only [FIo_Native.aspis_core.field.P, FIo_Native.fast_pairing.canonical.P,
    lift, bind_tc_ok]
  change (if UScalar.cast .U32 m ≥ 2147483647#u32
    then ok (U32.wrapping_sub (UScalar.cast .U32 m) 2147483647#u32)
    else ok (UScalar.cast .U32 m)) =
    (if m ≥ 2147483647#u64
    then ok (UScalar.cast .U32 (U64.wrapping_sub m 2147483647#u64))
    else ok (UScalar.cast .U32 m))
  split
  · rename_i h
    have hm : m ≥ 2147483647#u64 := by scalar_tac
    rw [if_pos hm]
    congr 1
    apply UScalar.eq_of_val_eq
    unfold U32.wrapping_sub U64.wrapping_sub
    rw [UScalar.cast_val_eq, UScalar.wrapping_sub_val_eq,
      UScalar.wrapping_sub_val_eq]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits,U32.size,U32.numBits]
    omega
  · rename_i h
    have hm : ¬m ≥ 2147483647#u64 := by scalar_tac
    rw [if_neg hm]

/-- Total exact base-field reduction on every source word. -/
theorem source (x : U64) : ∃ z,
    FIo_Native.aspis_core.field.reduce_u64 x = ok z ∧
    z.val = x.val % 2147483647 ∧ z.val < 2147483647 := by
  rw [same]
  exact LPf_ReductionWord.native_reduce x

#print axioms same
#print axioms source
end AspisR1.LPf_CoreReduction

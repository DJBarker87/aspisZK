import JFs_TX2_FoldLane
set_option autoImplicit false
namespace AspisR1.JFs_TX2_CanonicalReduce
open Aeneas Aeneas.Std Result

theorem twice_bound (x : U64) : (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)).val≤2147483651 := by
  change (UScalar.wrapping_add ((FIo_ReduceBounds.fold x) &&& 2147483647#u64)
    (U64.wrapping_shr (FIo_ReduceBounds.fold x) 31#u32)).val≤2147483651
  rw [UScalar.wrapping_add_val_eq,Nat.mod_eq_of_lt (FIo_ReduceBounds.sum_bound _)]
  have lo:=FIo_ReduceFacts.low (FIo_ReduceBounds.fold x)
  have first:=JFs_TX2_FoldLane.fold_bound x
  have shift:=FIo_ReduceBounds.shr_val (FIo_ReduceBounds.fold x)
  change _ + _ ≤2147483651
  unfold JFs_TX2_FoldLane.R at first
  omega

theorem source (x : U64) : ∃ z, FIo_Native.fast_pairing.canonical.reduce x=ok z ∧ z.val<2147483647 := by
  have small:=twice_bound x
  unfold FIo_Native.fast_pairing.canonical.reduce
  simp only [FIo_Native.fast_pairing.canonical.P,lift,bind_tc_ok]
  change ∃ z, (if FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)≥2147483647#u64
    then ok (UScalar.cast .U32 (U64.wrapping_sub (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)) 2147483647#u64))
    else ok (UScalar.cast .U32 (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x))))=ok z ∧ z.val<2147483647
  split
  · rename_i h
    refine ⟨_,rfl,?_⟩
    unfold U64.wrapping_sub
    rw [UScalar.cast_val_eq,UScalar.wrapping_sub_val_eq]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits,U32.size,U32.numBits]
    have lower : 2147483647≤(FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)).val := by scalar_tac
    omega
  · rename_i h
    refine ⟨_,rfl,?_⟩
    scalar_tac

#print axioms twice_bound
#print axioms source
end AspisR1.JFs_TX2_CanonicalReduce

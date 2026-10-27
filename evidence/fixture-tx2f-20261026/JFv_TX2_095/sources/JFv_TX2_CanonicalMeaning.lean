import JFs_TX2_CanonicalReduce
import JFv_TX2_FoldResidue
set_option autoImplicit false
namespace AspisR1.JFv_TX2_CanonicalMeaning
open Aeneas Aeneas.Std Result

theorem source (x : U64) (z : U32)
    (run : FIo_Native.fast_pairing.canonical.reduce x=ok z) : z.val=x.val%2147483647 := by
  let f := FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)
  have small : f.val≤2147483651 := JFs_TX2_CanonicalReduce.twice_bound x
  have residue : f.val%2147483647=x.val%2147483647 := by
    dsimp only [f]
    rw [JFv_TX2_FoldValue.source,JFv_TX2_FoldValue.source,
      JFv_TX2_FoldResidue.source,JFv_TX2_FoldResidue.source]
  unfold FIo_Native.fast_pairing.canonical.reduce at run
  simp only [FIo_Native.fast_pairing.canonical.P,lift,bind_tc_ok] at run
  change (if f≥2147483647#u64
    then ok (UScalar.cast .U32 (U64.wrapping_sub f 2147483647#u64))
    else ok (UScalar.cast .U32 f))=ok z at run
  split at run
  · rename_i lower
    have lower' : 2147483647≤f.val := by scalar_tac
    have same := Result.ok.inj run
    subst z
    unfold U64.wrapping_sub
    rw [UScalar.cast_val_eq,UScalar.wrapping_sub_val_eq]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits,U32.size,U32.numBits]
    have eq : f.val+(18446744073709551616-2147483647)=18446744073709551616+(f.val-2147483647) := by omega
    rw [eq,Nat.add_mod]
    norm_num only [Nat.reduceMod,Nat.zero_add,Nat.mod_mod]
    rw [Nat.mod_eq_of_lt (by omega : f.val-2147483647<4294967296)]
    have mod : f.val%2147483647=f.val-2147483647 := by omega
    exact mod.symm.trans residue
  · rename_i upper
    have upper' : f.val<2147483647 := by scalar_tac
    have same := Result.ok.inj run
    subst z
    rw [UScalar.cast_val_eq,Nat.mod_eq_of_lt (by
      norm_num [UScalar.size,UScalarTy.numBits,U32.size,U32.numBits]
      omega)]
    exact (Nat.mod_eq_of_lt upper').symm.trans residue
#print axioms source
end AspisR1.JFv_TX2_CanonicalMeaning

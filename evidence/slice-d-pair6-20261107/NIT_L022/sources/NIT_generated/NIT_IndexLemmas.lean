import NIT_PairComposition
set_option autoImplicit false
namespace AspisR1.NIT_IndexLemmas
open Aeneas Aeneas.Std Result

theorem mask (j : Usize) : (j &&& 3#usize).val=j.val%4 := by
 rw [UScalar.val_and]
 exact Nat.and_two_pow_sub_one_eq_mod j.val 2

theorem shift (j : Usize) : (Usize.wrapping_shr j 2#u32).val=j.val/4 := by
 have hb : 2<UScalarTy.Usize.numBits := by
  rw [UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h|h <;> omega
 change (UScalar.wrapping_shr j 2#u32).bv.toNat=j.val/4
 rw [UScalar.wrapping_shr_bv_eq]
 have h := BitVec.toNat_ushiftRight j.bv ((2#u32).val % UScalarTy.Usize.numBits)
 simpa only [show (2#u32).val=2 by rfl,Nat.mod_eq_of_lt hb,Nat.shiftRight_eq_div_pow,BitVec.ushiftRight_eq,show (2:Nat)^2=4 by rfl] using h

theorem perm (i : Usize) (small : i.val<4) :
 ∃ output,Array.index_usize FIo_Native.weights.PERM i=ok output ∧
 output.val=NIT_Cuts.perm i.val ∧ output.val<4 := by
 have cases4 : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
 rcases cases4 with h|h|h|h
 · have same : i=0#usize := UScalar.eq_of_val_eq h
   subst i; exact ⟨0#usize,by simp [FIo_Native.weights.PERM,Array.index_usize,Array.make],rfl,by decide⟩
 · have same : i=1#usize := UScalar.eq_of_val_eq h
   subst i; exact ⟨3#usize,by simp [FIo_Native.weights.PERM,Array.index_usize,Array.make],rfl,by decide⟩
 · have same : i=2#usize := UScalar.eq_of_val_eq h
   subst i; exact ⟨2#usize,by simp [FIo_Native.weights.PERM,Array.index_usize,Array.make],rfl,by decide⟩
 · have same : i=3#usize := UScalar.eq_of_val_eq h
   subst i; exact ⟨1#usize,by simp [FIo_Native.weights.PERM,Array.index_usize,Array.make],rfl,by decide⟩

#print axioms mask
#print axioms shift
#print axioms perm
end AspisR1.NIT_IndexLemmas

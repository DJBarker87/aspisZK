import NHI_ScalarDomain
set_option autoImplicit false
namespace NIG_Indices
open Aeneas Aeneas.Std Result

theorem shift_two (j:Usize) :
 (Usize.wrapping_shr j 2#u32).val=j.val/4 := by
 change (j.bv.ushiftRight (2%UScalarTy.Usize.numBits)).toNat=j.val/4
 rw [BitVec.ushiftRight_eq,BitVec.toNat_ushiftRight,UScalar.bv_toNat]
 have bound:2<UScalarTy.Usize.numBits:=by
  change 2<System.Platform.numBits
  have lower:=System.Platform.le_numBits
  omega
 rw [Nat.mod_eq_of_lt bound,Nat.shiftRight_eq_div_pow]
 rfl

theorem common (j:Usize) (hj:j.val<16) :
 (j &&& 3#usize).val=j.val%4 ∧
 (Usize.wrapping_shr j 2#u32).val=j.val/4 ∧
 (j &&& 3#usize).val<4 ∧ (Usize.wrapping_shr j 2#u32).val<4 := by
 rw [shift_two]
 have cases16 : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 ∨ j.val=4 ∨ j.val=5 ∨ j.val=6 ∨ j.val=7 ∨ j.val=8 ∨ j.val=9 ∨ j.val=10 ∨ j.val=11 ∨ j.val=12 ∨ j.val=13 ∨ j.val=14 ∨ j.val=15 := by omega
 rcases cases16 with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
 · have same:j=0#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=1#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=2#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=3#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=4#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=5#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=6#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=7#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=8#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=9#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=10#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=11#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=12#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=13#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=14#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide
 · have same:j=15#usize:=UScalar.eq_of_val_eq h
   rw [same]
   decide

theorem low (j:Usize) (hj:j.val<16) :
 ∃ lo hi:Usize, j%4#usize=ok lo ∧ j/4#usize=ok hi ∧
 lo.val=j.val%4 ∧ hi.val=j.val/4 ∧ lo.val<4 ∧ hi.val<4 := by
 have cases16 : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 ∨ j.val=4 ∨ j.val=5 ∨ j.val=6 ∨ j.val=7 ∨ j.val=8 ∨ j.val=9 ∨ j.val=10 ∨ j.val=11 ∨ j.val=12 ∨ j.val=13 ∨ j.val=14 ∨ j.val=15 := by omega
 rcases cases16 with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
 · have same:j=0#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨0#usize,0#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=1#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨1#usize,0#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=2#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨2#usize,0#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=3#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨3#usize,0#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=4#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨0#usize,1#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=5#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨1#usize,1#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=6#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨2#usize,1#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=7#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨3#usize,1#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=8#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨0#usize,2#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=9#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨1#usize,2#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=10#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨2#usize,2#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=11#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨3#usize,2#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=12#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨0#usize,3#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=13#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨1#usize,3#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=14#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨2#usize,3#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩
 · have same:j=15#usize:=UScalar.eq_of_val_eq h
   rw [same]
   exact ⟨3#usize,3#usize,rfl,rfl,by decide,by decide,by decide,by decide⟩

#print axioms shift_two
#print axioms common
#print axioms low
end NIG_Indices

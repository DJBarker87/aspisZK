import NHI_KindDomain
set_option autoImplicit false
namespace NHX_KindIndex
open Aeneas Aeneas.Std Result

def native (kind : Usize) : Usize :=
 if kind<4#usize then Usize.wrapping_sub kind 1#usize else Usize.wrapping_sub kind 2#usize

theorem value (kind : Usize) (member : kind.val=1 ∨ kind.val=2 ∨ kind.val=3 ∨ kind.val=5 ∨ kind.val=6) :
 (native kind).val=NHI_KindDomain.row kind.val := by
 have cap:16≤UScalar.size .Usize:=by
  rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h|h <;> simp [h]
 have small:kind.val≤6:=by rcases member with h|h|h|h|h <;> omega
 have positive:1≤kind.val:=by rcases member with h|h|h|h|h <;> omega
 unfold native
 by_cases h:kind<4#usize
 · have hv:kind.val<4:=h
   rw [if_pos h,Usize.wrapping_sub_val_eq]
   change (kind.val+(UScalar.size .Usize-1))%UScalar.size .Usize=NHI_KindDomain.row kind.val
   have eq:kind.val+(UScalar.size .Usize-1)=kind.val-1+UScalar.size .Usize:=by omega
   rw [eq,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega),NHI_KindDomain.row,if_pos hv]
 · have hv:¬kind.val<4:=h
   rw [if_neg h,Usize.wrapping_sub_val_eq]
   change (kind.val+(UScalar.size .Usize-2))%UScalar.size .Usize=NHI_KindDomain.row kind.val
   have eq:kind.val+(UScalar.size .Usize-2)=kind.val-2+UScalar.size .Usize:=by omega
   rw [eq,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega),NHI_KindDomain.row,if_neg hv]

theorem selected (kind : Usize) (member : kind.val=1 ∨ kind.val=2 ∨ kind.val=3 ∨ kind.val=5 ∨ kind.val=6) :
 (native kind).val<5 ∧ kind.val<7 := by
 rw [value kind member]
 exact NHI_KindDomain.selected kind.val member

theorem source (kind : Usize) :
 (if kind<4#usize then ok (Usize.wrapping_sub kind 1#usize) else ok (Usize.wrapping_sub kind 2#usize))=
 ok (native kind) := by
 by_cases h:kind<4#usize <;> simp only [native,h,ite_true,ite_false]

#print axioms value
#print axioms selected
#print axioms source
end NHX_KindIndex

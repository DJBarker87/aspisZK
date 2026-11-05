import NGW_FactorRow
set_option autoImplicit false
namespace NGW_FactorIndex
open Aeneas Aeneas.Std Result

theorem tau (d : Usize) (hd : d.val<5) :
 ∃ t,Array.index_usize FIn_WeightsExtract.TAU d=ok t ∧ t.val<5 := by
 have cases : d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 ∨ d.val=4 := by omega
 rcases cases with h|h|h|h|h
 · have same : d=0#usize := UScalar.eq_of_val_eq h
   subst d
   exact ⟨3#usize,rfl,by decide⟩
 · have same : d=1#usize := UScalar.eq_of_val_eq h
   subst d
   exact ⟨4#usize,rfl,by decide⟩
 · have same : d=2#usize := UScalar.eq_of_val_eq h
   subst d
   exact ⟨2#usize,rfl,by decide⟩
 · have same : d=3#usize := UScalar.eq_of_val_eq h
   subst d
   exact ⟨0#usize,rfl,by decide⟩
 · have same : d=4#usize := UScalar.eq_of_val_eq h
   subst d
   exact ⟨1#usize,rfl,by decide⟩

theorem coordinates (t : Usize) (ht : t.val<5) :
 (Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize t)).val<10 ∧
 (Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize t)).val<10 := by
 scalar_tac

#print axioms tau
#print axioms coordinates
end NGW_FactorIndex

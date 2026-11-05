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
   exact ⟨3#usize,(by unfold FIn_WeightsExtract.TAU; rfl),by decide⟩
 · have same : d=1#usize := UScalar.eq_of_val_eq h
   subst d
   exact ⟨4#usize,(by unfold FIn_WeightsExtract.TAU; rfl),by decide⟩
 · have same : d=2#usize := UScalar.eq_of_val_eq h
   subst d
   exact ⟨2#usize,(by unfold FIn_WeightsExtract.TAU; rfl),by decide⟩
 · have same : d=3#usize := UScalar.eq_of_val_eq h
   subst d
   exact ⟨0#usize,(by unfold FIn_WeightsExtract.TAU; rfl),by decide⟩
 · have same : d=4#usize := UScalar.eq_of_val_eq h
   subst d
   exact ⟨1#usize,(by unfold FIn_WeightsExtract.TAU; rfl),by decide⟩

theorem coordinates (t : Usize) (ht : t.val<5) :
 (Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize t)).val<10 ∧
 (Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize t)).val<10 := by
 have cases : t.val=0 ∨ t.val=1 ∨ t.val=2 ∨ t.val=3 ∨ t.val=4 := by omega
 rcases cases with h|h|h|h|h
 · have same : t=0#usize := UScalar.eq_of_val_eq h
   subst t
   decide
 · have same : t=1#usize := UScalar.eq_of_val_eq h
   subst t
   decide
 · have same : t=2#usize := UScalar.eq_of_val_eq h
   subst t
   decide
 · have same : t=3#usize := UScalar.eq_of_val_eq h
   subst t
   decide
 · have same : t=4#usize := UScalar.eq_of_val_eq h
   subst t
   decide

#print axioms tau
#print axioms coordinates
end NGW_FactorIndex

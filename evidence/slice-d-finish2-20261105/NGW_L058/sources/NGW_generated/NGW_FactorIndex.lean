import NGW_FactorRow
import NGW_Usize
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
 have size : 4096≤UScalar.size .Usize := by
  rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h|h <;> simp [h]
 have mv : (Usize.wrapping_mul 2#usize t).val=2*t.val := by
  rw [Usize.wrapping_mul_val_eq]
  change (2*t.val)%UScalar.size .Usize=2*t.val
  apply Nat.mod_eq_of_lt
  omega
 rw [NGW_Usize.sub_value _ _ (by rw [mv];change 2*t.val≤9;omega),
     NGW_Usize.sub_value _ _ (by rw [mv];change 2*t.val≤8;omega),mv]
 change 9-2*t.val<10 ∧ 8-2*t.val<10
 omega

#print axioms tau
#print axioms coordinates
end NGW_FactorIndex

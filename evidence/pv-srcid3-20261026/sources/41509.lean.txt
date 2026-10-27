import R1Z.PV_Src_ExternalBlockStep

/-! Locality of a four-word block write: all other blocks retain their exact
words. This is the invariant needed for the in-place source implementation. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalBlockWrite
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_ExternalBlockStep

theorem other (s : State) (g : Usize) (hg : g.val < 4)
    (m : Array U32 4#usize) (j : Nat) (hj : j < 4*g.val ∨ 4*g.val+4 ≤ j) :
    (write s g m).val[j]! = s.val[j]! := by
  unfold write
  rw [BuilderRecordsArray.set_get _ _ _ j (by rw [offset_val g hg _ (by decide)];simp;omega),
    if_neg (by rw [offset_val g hg _ (by decide)];simp;omega)]
  rw [BuilderRecordsArray.set_get _ _ _ j (by rw [offset_val g hg _ (by decide)];simp;omega),
    if_neg (by rw [offset_val g hg _ (by decide)];simp;omega)]
  rw [BuilderRecordsArray.set_get _ _ _ j (by rw [offset_val g hg _ (by decide)];simp;omega),
    if_neg (by rw [offset_val g hg _ (by decide)];simp;omega)]
  rw [BuilderRecordsArray.set_get _ _ _ j (by rw [base_val g hg];simp;omega),
    if_neg (by rw [base_val g hg];omega)]

theorem suffix (original current : State) (g : Usize) (hg : g.val < 4)
    (m : Array U32 4#usize)
    (h : ∀ j, 4*g.val ≤ j → j < 16 → current.val[j]! = original.val[j]!) :
    ∀ j, 4*(Usize.wrapping_add g 1#usize).val ≤ j → j < 16 →
      (write current g m).val[j]! = original.val[j]! := by
  intro j hj hn
  have next := BuilderRecordsArray.next_val g (by omega)
  rw [next] at hj
  rw [other current g hg m j (Or.inr (by omega))]
  exact h j (by omega) hn

#print axioms other
#print axioms suffix
end R1Z.PV_Src_ExternalBlockWrite

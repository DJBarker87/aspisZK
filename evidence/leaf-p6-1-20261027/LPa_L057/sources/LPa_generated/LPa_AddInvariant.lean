import LPa_AddFormula
open Aeneas Aeneas.Std
open XRk_Release
set_option autoImplicit false
namespace LPa.Add

def Canonical (q : aspis_core.field.QM31) : Prop :=
  q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
  q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647

theorem word_canonical (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    (word a b).val < 2147483647 := by
  rw [word_val_canonical a b ha hb]
  split <;> omega

theorem field_canonical (a b : aspis_core.field.QM31) (ha : Canonical a) (hb : Canonical b) :
    Canonical (field a b) := by
  exact ⟨word_canonical _ _ ha.1 hb.1,
    word_canonical _ _ ha.2.1 hb.2.1,
    word_canonical _ _ ha.2.2.1 hb.2.2.1,
    word_canonical _ _ ha.2.2.2 hb.2.2.2⟩

theorem fold_canonical (xs : List aspis_core.field.QM31)
    (coefficients : ∀ q ∈ xs, Canonical q) (seed : aspis_core.field.QM31) (initial : Canonical seed) :
    Canonical (xs.foldl field seed) := by
  induction xs generalizing seed with
  | nil => exact initial
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro q hq
      exact coefficients q (by simp only [List.mem_cons]; exact Or.inr hq)
    · exact field_canonical seed x initial (coefficients x (by simp))

#print axioms word_canonical
#print axioms field_canonical
#print axioms fold_canonical
end LPa.Add

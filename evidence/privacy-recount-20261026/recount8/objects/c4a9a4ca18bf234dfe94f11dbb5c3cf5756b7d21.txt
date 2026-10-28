import R1Z.PV_RDCD_SliceArrayBinding
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD_GenericArrayEq
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem list_compare {A : Type} (p : core.cmp.PartialEq A A)
    (hn : ∀ a b, p.ne a b = ok (decide (a≠b)))
    (xs ys : List A) (lengths : xs.length=ys.length) :
    List.allM (PV_RDCD_Slice194.compare p) (xs.zip ys) = ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all; rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp_all
    | cons b ys =>
      have lens : xs.length=ys.length := by simpa using lengths
      by_cases h : a=b
      · subst b
        simpa [List.zip_cons_cons,List.allM,PV_RDCD_Slice194.compare,hn] using ih ys lens
      · simp [List.zip_cons_cons,List.allM,PV_RDCD_Slice194.compare,hn,h]
        rfl

theorem array_eq {A : Type} {N : Usize} (p : core.cmp.PartialEq A A)
    (hn : ∀ a b, p.ne a b = ok (decide (a≠b))) (a b : Array A N) :
    core.array.equality.PartialEqArray.eq p a b = ok (decide (a=b)) := by
  rw [← PV_RDCD_SliceArrayBinding.array_binding]
  rw [PV_RDCD_Slice194.source_model]
  have lengths : a.val.length=b.val.length := by rw [a.property,b.property]
  simp only [lengths,ite_true]
  rw [list_compare p hn _ _ lengths]
  congr 2
  exact propext Subtype.val_inj

/-- Default ne preserves a complete Eq law, including the absence of errors. -/
theorem default_ne {A : Type} (eq : A → A → Result Bool)
    (h : ∀ a b, eq a b = ok (decide (a=b))) (a b : A) :
    (do let e ← eq a b; ok (!e)) = ok (decide (a≠b)) := by
  rw [h]
  by_cases he : a=b <;> simp [he]
#print axioms list_compare
#print axioms array_eq
#print axioms default_ne
end R1Z.PV_RDCD_GenericArrayEq

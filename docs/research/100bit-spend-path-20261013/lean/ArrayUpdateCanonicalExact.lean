import SelectorExpansionCorrectness

/-! Reuse the symbolic update proof shape of SelectorExpansionCorrectness
(set_canonical and decodedArray_set), exposing the raw cell frame for callers.
No array contents or concrete finite-field terms are evaluated. -/
set_option autoImplicit false
namespace AspisR1.ArrayUpdateCanonicalExact
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a

def cells {n : Usize} (a : Array QM n) (i : Fin n.val) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

/-- Actual checked update, canonicality, and the complete pointwise frame.
The input and updated cell are the only canonicality premises. -/
theorem update_success {n : Usize} (a : Array QM n) (i : Usize) (x : QM)
    (hi : i.val < n.val) (ha : CanonicalArray a) (hx : CanonicalQM x) :
    ∃ out, Array.update a i x = .ok out ∧ CanonicalArray out ∧
      cells out = Function.update (cells a) ⟨i.val, hi⟩ x := by
  obtain ⟨out, hr, hs⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by simpa [a.property] using hi))
  have hcell : ∀ j : Fin n.val,
      cells out j = if j.val = i.val then x else cells a j := by
    intro j
    cases hs
    have hj0 : j.val < a.val.length := by simpa [a.property] using j.isLt
    have hjSet : j.val < (a.val.set i.val x).length := by simpa using hj0
    change (a.val.set i.val x)[j.val]'hjSet = _
    by_cases he : i.val = j.val
    · rw [if_pos he.symm]
      have hself := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [he] using hj0)
      simpa [he] using hself
    · rw [if_neg (Ne.symm he)]
      exact List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val) he hjSet
  refine ⟨out, hr, ?_, ?_⟩
  · intro j
    change CanonicalQM (cells out j)
    rw [hcell]
    split
    · exact hx
    · exact ha j
  · funext j
    rw [hcell]
    by_cases he : j = (⟨i.val, hi⟩ : Fin n.val)
    · subst j
      simp
    · have hv : j.val ≠ i.val := by
        intro h
        exact he (Fin.ext h)
      simp [Function.update, he, hv]

#print axioms update_success
end AspisR1.ArrayUpdateCanonicalExact

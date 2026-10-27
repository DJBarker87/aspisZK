import LPf_ReductionWord
set_option autoImplicit false
namespace AspisR1.LPf_ArrayFour
open Aeneas Aeneas.Std

theorem list_shape {α : Type} (xs : List α) (h : xs.length = 4) :
    ∃ a b c d, xs = [a,b,c,d] := by
  rcases xs with _ | ⟨a,xs⟩
  · simp at h
  rcases xs with _ | ⟨b,xs⟩
  · simp at h
  rcases xs with _ | ⟨c,xs⟩
  · simp at h
  rcases xs with _ | ⟨d,xs⟩
  · simp at h
  have hz : xs.length = 0 := by
    simp only [List.length_cons] at h
    omega
  cases xs with
  | nil => exact ⟨a,b,c,d,rfl⟩
  | cons e rest => simp at hz

theorem shape {α : Type} (xs : Array α 4#usize) :
    ∃ a b c d, xs = Array.make 4#usize [a,b,c,d] := by
  obtain ⟨a,b,c,d,h⟩ := list_shape xs.val (by simpa using xs.property)
  refine ⟨a,b,c,d,?_⟩
  apply Subtype.ext
  exact h

#print axioms list_shape
#print axioms shape
end AspisR1.LPf_ArrayFour

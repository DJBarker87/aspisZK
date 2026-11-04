import Aeneas
set_option autoImplicit false
namespace AspisR1.NFA_ArrayShape
open Aeneas Aeneas.Std Result
def pack {α : Type} (a b c d e f g h : α) : Array α 8#usize :=
  Array.make 8#usize [a,b,c,d,e,f,g,h]
theorem shape {α : Type} (a : Array α 8#usize) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, a=pack a0 a1 a2 a3 a4 a5 a6 a7 := by
  rcases a with ⟨xs,h⟩
  change xs.length=8 at h
  cases xs with
  | nil => simp at h
  | cons a0 xs =>
    cases xs with
    | nil => simp at h
    | cons a1 xs =>
      cases xs with
      | nil => simp at h
      | cons a2 xs =>
        cases xs with
        | nil => simp at h
        | cons a3 xs =>
          cases xs with
          | nil => simp at h
          | cons a4 xs =>
            cases xs with
            | nil => simp at h
            | cons a5 xs =>
              cases xs with
              | nil => simp at h
              | cons a6 xs =>
                cases xs with
                | nil => simp at h
                | cons a7 xs =>
                  cases xs with
                  | nil => exact ⟨a0,a1,a2,a3,a4,a5,a6,a7,rfl⟩
                  | cons a8 xs => simp at h

#print axioms shape
end AspisR1.NFA_ArrayShape

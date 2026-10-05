import Mathlib.Tactic.Omega

set_option autoImplicit false
namespace AspisV8R19.R816Fin222ActiveSupplementDispatch

def activePos (i : Fin 214) : Fin 222 := Fin.castLE (by decide) i

def supplementPos (i : Fin 8) : Fin 222 :=
  ⟨214 + i.val, by have hi := i.isLt; omega⟩

theorem fin222_from_active_and_supplement {P : Fin 222 → Prop}
    (hactive : ∀ i : Fin 214, P (activePos i))
    (hsupplement : ∀ i : Fin 8, P (supplementPos i)) :
    ∀ i : Fin 222, P i := by
  intro i
  by_cases h : i.val < 214
  · let j : Fin 214 := ⟨i.val, h⟩
    have hpos : activePos j = i := by
      apply Fin.ext
      rfl
    rw [← hpos]
    exact hactive j
  · let j : Fin 8 := ⟨i.val - 214, by have hi := i.isLt; omega⟩
    have hpos : supplementPos j = i := by
      apply Fin.ext
      simp [supplementPos]
      omega
    rw [← hpos]
    exact hsupplement j

#print axioms fin222_from_active_and_supplement
end AspisV8R19.R816Fin222ActiveSupplementDispatch

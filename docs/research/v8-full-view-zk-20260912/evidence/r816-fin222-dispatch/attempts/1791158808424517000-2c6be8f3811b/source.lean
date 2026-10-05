set_option autoImplicit false
namespace AspisV8R19.R816Fin222ActiveSupplementDispatch

def activePos (i : Fin 214) : Fin 222 := Fin.castLE (by decide) i

def supplementPos (i : Fin 8) : Fin 222 :=
  ⟨214 + i.val, by
    have h := Nat.add_lt_add_left i.isLt 214
    simpa using h⟩

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
  · have hle : 214 ≤ i.val := Nat.not_lt.mp h
    let j : Fin 8 := ⟨i.val - 214, by
      have hsum : (i.val - 214) + 214 < 8 + 214 := by
        simpa [Nat.sub_add_cancel hle] using i.isLt
      exact Nat.add_lt_add_iff_right.mp hsum⟩
    have hpos : supplementPos j = i := by
      apply Fin.ext
      change 214 + (i.val - 214) = i.val
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel hle
    rw [← hpos]
    exact hsupplement j

#print axioms fin222_from_active_and_supplement
end AspisV8R19.R816Fin222ActiveSupplementDispatch

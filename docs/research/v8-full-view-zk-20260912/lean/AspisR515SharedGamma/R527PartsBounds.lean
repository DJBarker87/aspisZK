import AspisR515SharedGamma.SharedGammaDots

set_option autoImplicit false

namespace AspisV8.SharedGammaDots

private theorem mod_p_le_m (n : Nat) : n % AspisV8.AffinePrimal.p ≤ AspisV8.AffinePrimal.m := by
  have hp : 0 < AspisV8.AffinePrimal.p := by norm_num [AspisV8.AffinePrimal.p]
  have h := Nat.mod_lt n hp
  have hle : n % AspisV8.AffinePrimal.p ≤ AspisV8.AffinePrimal.p - 1 :=
    Nat.le_pred_of_lt h
  simpa [AspisV8.AffinePrimal.m] using hle

theorem partsN_entry_le_m (x : AspisV8.SemanticCarry.Q Nat)
    (hx : ∀ j : Fin 4, x j ≤ AspisV8.AffinePrimal.m) :
    ∀ i j : Fin 3, partsN x i j ≤ AspisV8.AffinePrimal.m := by
  intro i j
  have hx0 := hx 0
  have hx1 := hx 1
  have hx2 := hx 2
  have hx3 := hx 3
  fin_cases i <;> fin_cases j <;> simp [partsN] <;>
    first | omega | exact mod_p_le_m _

theorem productsN_entry_le_m_sq (x y : AspisV8.SemanticCarry.Q Nat)
    (hx : ∀ j : Fin 4, x j ≤ AspisV8.AffinePrimal.m)
    (hy : ∀ j : Fin 4, y j ≤ AspisV8.AffinePrimal.m) :
    ∀ i j : Fin 3,
      productsN x y i j ≤ AspisV8.AffinePrimal.m ^ 2 := by
  intro i j
  have h1 := partsN_entry_le_m x hx i j
  have h2 := partsN_entry_le_m y hy i j
  simpa [productsN, pow_two] using Nat.mul_le_mul h1 h2


theorem partsN_entry_canonical (x : AspisV8.SemanticCarry.Q Nat)
    (hx : ∀ j : Fin 4, x j < AspisV8.AffinePrimal.p) :
    ∀ i j : Fin 3, partsN x i j < AspisV8.AffinePrimal.p := by
  have hb : ∀ j : Fin 4, x j ≤ AspisV8.AffinePrimal.m := by
    intro j
    have h := hx j
    unfold AspisV8.AffinePrimal.m
    exact Nat.le_pred_of_lt h
  intro i j
  have h := partsN_entry_le_m x hb i j
  have hp : 0 < AspisV8.AffinePrimal.p := by norm_num [AspisV8.AffinePrimal.p]
  unfold AspisV8.AffinePrimal.m at h
  omega

#print axioms partsN_entry_canonical

#print axioms partsN_entry_le_m
#print axioms productsN_entry_le_m_sq

end AspisV8.SharedGammaDots

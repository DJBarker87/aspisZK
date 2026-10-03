import AspisR515SharedGamma.SharedGammaDots

set_option autoImplicit false

namespace AspisV8.SharedGammaDots

private theorem mod_p_le_m (n : Nat) : n % AspisV8.AffinePrimal.p ≤ AspisV8.AffinePrimal.m := by
  have hp : 0 < AspisV8.AffinePrimal.p := by norm_num [AspisV8.AffinePrimal.p]
  have h := Nat.mod_lt n hp
  unfold AspisV8.AffinePrimal.p AspisV8.AffinePrimal.m at *
  omega

theorem partsN_entry_le_m (x : Q Nat)
    (hx : ∀ j : Fin 4, x j ≤ AspisV8.AffinePrimal.m) :
    ∀ i j : Fin 3, partsN x i j ≤ AspisV8.AffinePrimal.m := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [partsN] <;>
    try exact hx _ <;>
    try exact mod_p_le_m _

theorem productsN_entry_le_m_sq (x y : Q Nat)
    (hx : ∀ j : Fin 4, x j ≤ AspisV8.AffinePrimal.m)
    (hy : ∀ j : Fin 4, y j ≤ AspisV8.AffinePrimal.m) :
    ∀ i j : Fin 3,
      productsN x y i j ≤ AspisV8.AffinePrimal.m ^ 2 := by
  intro i j
  have h1 := partsN_entry_le_m x hx i j
  have h2 := partsN_entry_le_m y hy i j
  simpa [productsN, pow_two] using Nat.mul_le_mul h1 h2

#print axioms partsN_entry_le_m
#print axioms productsN_entry_le_m_sq

end AspisV8.SharedGammaDots

import R1Z.PV_RunJoin_E1Product
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_E1Joint

/-- Product-completion density after fixing the external fault world. `Rest`
is the retained independent completion/oracle carrier. The pointwise native
factorization is a separate V339 obligation; it is never a definition of
native execution or native availability. -/
def weight {C R Coins Rest : Type} [Fintype R] [Fintype Rest]
    (n : Nat) (law : C → R → ℚ) (context : Fin n → (Fin n → R) × Rest → C)
    (coordinates : Coins ≃ (Fin n → R) × Rest) (c : Coins) : ℚ :=
  (∏ i, law (context i (coordinates c)) ((coordinates c).1 i)) / Fintype.card Rest

theorem uniform {C R Coins Rest : Type} [Fintype R] [Fintype Rest] [Fintype Coins]
    (n : Nat) (law : C → R → ℚ)
    (e1 : ∀ c r, law c r = 1 / (Fintype.card R : ℚ))
    (context : Fin n → (Fin n → R) × Rest → C)
    (coordinates : Coins ≃ (Fin n → R) × Rest) (c : Coins) :
    weight n law context coordinates c = 1 / (Fintype.card Coins : ℚ) := by
  unfold weight
  rw [PV_RunJoin_E1Product.product_uniform law e1 n
    (fun i t => context i (t,(coordinates c).2)) (coordinates c).1]
  rw [Fintype.card_congr coordinates,Fintype.card_prod,Nat.cast_mul,div_div]

theorem native_density_uniform {C R Coins Rest : Type}
    [Fintype R] [Fintype Rest] [Fintype Coins]
    (n : Nat) (law : C → R → ℚ)
    (e1 : ∀ c r, law c r = 1 / (Fintype.card R : ℚ))
    (context : Fin n → (Fin n → R) × Rest → C)
    (coordinates : Coins ≃ (Fin n → R) × Rest) (nativeWeight : Coins → ℚ)
    (factorization_V339 : ∀ c, nativeWeight c = weight n law context coordinates c) (c : Coins) :
    nativeWeight c = 1 / (Fintype.card Coins : ℚ) :=
  (factorization_V339 c).trans (uniform n law e1 context coordinates c)

theorem native_test {C R Coins Rest : Type}
    [Fintype R] [Fintype Rest] [Fintype Coins]
    (n : Nat) (law : C → R → ℚ)
    (e1 : ∀ c r, law c r = 1 / (Fintype.card R : ℚ))
    (context : Fin n → (Fin n → R) × Rest → C)
    (coordinates : Coins ≃ (Fin n → R) × Rest) (nativeWeight : Coins → ℚ)
    (factorization_V339 : ∀ c, nativeWeight c = weight n law context coordinates c) (f : Coins → ℚ) :
    (∑ c, nativeWeight c * f c) = (∑ c, f c) / Fintype.card Coins := by
  simp_rw [native_density_uniform n law e1 context coordinates nativeWeight factorization_V339]
  simp only [one_div_mul_eq_div,Finset.sum_div]

#print axioms uniform
#print axioms native_density_uniform
#print axioms native_test
end R1Z.PV_RunJoin_E1Joint

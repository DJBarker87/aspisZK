import AspisV8R19.R417Q22SuccessLaw
import Mathlib.Tactic

/-! Step 7 is only a statement about the uniform subset law. The imported
q22 kernel theorem includes its success mass and does not assert a shared
oracle or Fiat--Shamir law. -/
set_option autoImplicit false
namespace AspisR0.QueryLaw
noncomputable section

theorem source_uniform_success : type_of% AspisV8R19.R417Q22SuccessLaw.uniform_success :=
  AspisV8R19.R417Q22SuccessLaw.uniform_success

def successfulSets (M : Finset (Fin 262144)) (q : Nat) : Finset (Finset (Fin 262144)) :=
  (Finset.univ.powersetCard q).filter fun S => S ⊆ M

theorem successfulSets_eq (M : Finset (Fin 262144)) (q : Nat) :
    successfulSets M q = M.powersetCard q := by
  ext S
  simp only [successfulSets, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  exact and_comm

/-- Probability under the uniform q-subset law, written as its exact finite
count ratio. The q-subset space is nonempty when q ≤ 262144. -/
def uniformProbability (M : Finset (Fin 262144)) (q : Nat) : ℚ :=
  (successfulSets M q).card / (Finset.univ.powersetCard q : Finset (Finset (Fin 262144))).card

theorem uniform_subset_bound (M : Finset (Fin 262144)) (q : Nat)
    (hq : q ≤ 262144) (hM : M.card ≤ 9557) :
    uniformProbability M q = (M.card.choose q : ℚ)/(Nat.choose 262144 q : ℚ) ∧
    uniformProbability M q ≤ (Nat.choose 9557 q : ℚ)/(Nat.choose 262144 q : ℚ) := by
  have he : uniformProbability M q = (M.card.choose q : ℚ)/(Nat.choose 262144 q : ℚ) := by
    simp only [uniformProbability, successfulSets_eq, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
  refine ⟨he,?_⟩
  rw [he]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.choose_le_choose q hM
  · positivity

theorem uniform_q22_bound (M : Finset (Fin 262144)) (hM : M.card ≤ 9557) :
    uniformProbability M 22 ≤ (Nat.choose 9557 22 : ℚ)/(Nat.choose 262144 22 : ℚ) :=
  (uniform_subset_bound M 22 (by decide) hM).2

#print axioms source_uniform_success
#print axioms uniform_subset_bound
#print axioms uniform_q22_bound
end
end AspisR0.QueryLaw

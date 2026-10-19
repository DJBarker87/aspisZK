import R0.RoundNormalization
import R0.RoundCore

/-! F5 with the quarter explicitly restored by specification revision cd5eb4226.
KernelCorrespondence proves the other side of the shared RoundCore bridge. -/
set_option autoImplicit false
namespace AspisR0.Round
open AspisR0.Fold AspisR0.RoundNormalization
open AspisPool.AlgorithmicCircleDecoderV7
open Polynomial
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem fold_eq_core (alpha : K) (q : InitialMessage K) :
    foldMessage alpha q = RoundCore.fold alpha q := by
  funext d
  exact foldMessage_eq_sum alpha q d

theorem dual_eq_core (alpha : K) (w : InitialMessage K) :
    citedDualFold alpha w = RoundCore.dualFold alpha w := rfl

theorem polynomial_eq_core (q w : InitialMessage K) :
    roundPolynomial q w = RoundCore.polynomial q w := rfl

theorem quarter_eq_inverse_two_mul_two : quarter (K := K) = ((2 : K)*2)⁻¹ := by
  norm_num [quarter]

theorem quarter_ne_zero : quarter (K := K) ≠ 0 := by
  rw [quarter_eq_inverse_two_mul_two]
  exact inv_ne_zero (mul_ne_zero AspisWide.InitialEncoder.two_ne_zero
    AspisWide.InitialEncoder.two_ne_zero)

/-- Corrected F5, for precisely the message fold in F4. -/
theorem F5 (q w : InitialMessage K) :
    quarter (K := K) = ((2 : K)*2)⁻¹ ∧ quarter (K := K) ≠ 0 ∧
    (roundPolynomial q w).natDegree ≤ 6 ∧
    (∀ alpha, (roundPolynomial q w).eval alpha =
      quarter * dot (foldMessage alpha q) (citedDualFold alpha w)) ∧
    (roundPolynomial q w).coeff 0 + (roundPolynomial q w).coeff 4 = quarter * dot q w :=
  ⟨quarter_eq_inverse_two_mul_two, quarter_ne_zero, cited_round_identities q w⟩

theorem wideF5 : type_of% (@F5 AspisWideTower.WideExact _ _ (Classical.decEq _) _) :=
  @F5 AspisWideTower.WideExact _ _ (Classical.decEq _) _

/-- The coefficient comparison in §5 cancels exactly the nonzero quarter. -/
theorem boundary_claim (q w : InitialMessage K) (claimed : K[X]) (claim : K)
    (same : claimed = roundPolynomial q w)
    (boundary : claimed.coeff 0 + claimed.coeff 4 = quarter * claim) :
    dot q w = claim := by
  rw [same, round_boundary] at boundary
  exact (mul_left_cancel₀ quarter_ne_zero) boundary

#print axioms F5
#print axioms wideF5
#print axioms fold_eq_core
#print axioms dual_eq_core
#print axioms polynomial_eq_core
#print axioms boundary_claim
end
end AspisR0.Round

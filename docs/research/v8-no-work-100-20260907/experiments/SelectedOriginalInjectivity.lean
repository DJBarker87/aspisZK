import SelectedQuotientOriginal
import SelectedSimpleRootRigidity
import SelectedHigherYBranch

/-! Source-only draft: injectivity of the actual reconstructed original on
the selected image-valid quotient domain. The chord may vanish at two stored
symbols; no global denominator inverse or ambient-message image assumption
is added. Regular-branch uniqueness then applies to the SAME Qualified
quotients, even when they were selected at different post-alpha histories.
This is not unrestricted Data.original injectivity, extraction, or a
gamma/alpha/query probability theorem. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedOriginalInjectivity
open Polynomial Finset
noncomputable section

namespace Generic
variable {k I : Type*} [Field k] [DecidableEq I]

/-- Only the displayed evaluation set is needed; no enumeration of a large
concrete domain and no received-word polynomiality enter this argument. -/
theorem polynomial_eq_of_many_values
    (points : I → k) (injective : Function.Injective points)
    (S : Finset I) (P Q : k[X]) (D : Nat)
    (left : P.natDegree ≤ D) (right : Q.natDegree ≤ D)
    (many : D < S.card)
    (values : ∀ i ∈ S, P.eval (points i) = Q.eval (points i)) : P = Q := by
  classical
  by_contra different
  have nonzero : P - Q ≠ 0 := sub_ne_zero.mpr different
  have roots : (S.image points).val ⊆ (P - Q).roots := by
    intro t member
    change t ∈ S.image points at member
    obtain ⟨i, inside, rfl⟩ := Finset.mem_image.mp member
    apply (Polynomial.mem_roots nonzero).mpr
    change (P - Q).eval (points i) = 0
    rw [Polynomial.eval_sub, values i inside, sub_self]
  have degree : (P - Q).natDegree ≤ D :=
    (Polynomial.natDegree_sub_le P Q).trans (max_le left right)
  have bound : S.card ≤ D := calc
    S.card = (S.image points).card :=
      (Finset.card_image_of_injective _ injective).symm
    _ ≤ (P - Q).natDegree := Polynomial.card_le_degree_of_subset_roots roots
    _ ≤ D := degree
  exact (Nat.not_lt_of_ge bound) many
end Generic

open AspisV5ComponentCQM31TowerExact
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisK1.V7Tag73ExactGRSConversion
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.OODInterpolant AspisV8.GammaComponentGame
open AspisV8.SelectedQuotientOriginal AspisV8.ComponentOODBinding
open AspisV8.SelectedOODGate

abbrev K := QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

/-- Cancellation is requested only at this actual non-pole symbol. The
two literal image equations are used by encoded_original on both sides. -/
theorem encoded_eq_on_nonpole (d : Data (K := K)) (checked : d.Checked)
    (Q Q' : Fin 1024 → K)
    (image : Q 1023 = 0 ∧ d.b * Q 1022 - d.c * Q 1021 = 0)
    (image' : Q' 1023 = 0 ∧ d.b * Q' 1022 - d.c * Q' 1021 = 0)
    (same : d.original Q = d.original Q')
    (i : Fin 1048576) (nonpole : denominator d i ≠ 0) :
    exactInitialEncoder Q i = exactInitialEncoder Q' i := by
  have encoded := congrArg (fun message => exactInitialEncoder message i) same
  rw [encoded_original d checked Q image i,
    encoded_original d checked Q' image' i] at encoded
  exact mul_left_cancel₀ nonpole (add_right_cancel encoded)

/-- The actual stored GRS conversion, including its nonzero multiplier,
transports a symbol equality to the corresponding numerator evaluation. -/
theorem grs_eval_eq_of_encoded_eq (Q Q' : Fin 1024 → K)
    (i : Fin 1048576) (same : exactInitialEncoder Q i = exactInitialEncoder Q' i) :
    (exactCircleGRSPolynomial Q).eval (exactCircleGRSPoint i) =
      (exactCircleGRSPolynomial Q').eval (exactCircleGRSPoint i) := by
  rw [exactInitialEncoder_coordinate_grs Q i,
    exactInitialEncoder_coordinate_grs Q' i] at same
  exact mul_left_cancel₀ (exactCircleGRSMultiplier_ne_zero i) same

/-- Image-restricted source reconstruction is injective. There are at least
1048574 non-pole stored symbols, whereas both actual GRS numerator messages
have degree at most 1024. No assertion is made outside the image domain. -/
theorem original_injective_on_image (d : Data (K := K)) (checked : d.Checked)
    (Q Q' : Fin 1024 → K)
    (image : Q 1023 = 0 ∧ d.b * Q 1022 - d.c * Q 1021 = 0)
    (image' : Q' 1023 = 0 ∧ d.b * Q' 1022 - d.c * Q' 1021 = 0)
    (same : d.original Q = d.original Q') : Q = Q' := by
  let S : Finset (Fin 1048576) := Finset.univ \ poleSymbols d
  have cover : 1048576 ≤ S.card + (poleSymbols d).card := by
    simpa only [S, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_le_card_sdiff_add_card
        (s := (Finset.univ : Finset (Fin 1048576))) (t := poleSymbols d))
  have poles : (poleSymbols d).card ≤ 2 := poleSymbols_card d checked
  have many : 1024 < S.card := by omega
  apply exactCircleGRSPolynomial_injective
  apply Generic.polynomial_eq_of_many_values exactCircleGRSPoint
    exactCircleGRSPoint_injective S
    (exactCircleGRSPolynomial Q) (exactCircleGRSPolynomial Q') 1024
    (exactCircleGRSPolynomial_degree_le Q) (exactCircleGRSPolynomial_degree_le Q') many
  intro i inside
  have outside : i ∉ poleSymbols d := (Finset.mem_sdiff.mp inside).2
  have nonpole : denominator d i ≠ 0 := by
    intro zero
    exact outside (Finset.mem_filter.mpr ⟨Finset.mem_univ i, zero⟩)
  exact grs_eval_eq_of_encoded_eq Q Q' i
    (encoded_eq_on_nonpole d checked Q Q' image image' same i nonpole)

/-- Fix the received/OOD prefix, factor, row and gamma. Every actual
Qualified quotient on this regular branch is the same, without requiring
the prover to choose its final before alpha. No gamma-polynomial candidate
or component tuple is manufactured by this uniqueness statement. -/
theorem regular_qualified_unique
    (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (checked : d.Checked)
    (circles : d.x0 ^ 2 + d.y0 ^ 2 = 1 ∧ d.x1 ^ 2 + d.y1 ^ 2 = 1)
    (west : ∀ r, pointX d r ≠ -1) (F : TrivariatePolynomial K)
    (gamma : K) (Q Q' : Fin 1024 → K)
    (qualified : SelectedHigherYBranch.Qualified c1 c2 d F gamma Q)
    (qualified' : SelectedHigherYBranch.Qualified c1 c2 d F gamma Q')
    (r : Fin 2)
    (regular : (FactorCoherence.derivativeCurve F (point d r)
      (CurveOODGate.answerCurve (answers d r))).eval gamma ≠ 0) : Q = Q' := by
  have originals := SelectedSimpleRootRigidity.original_unique c1 c2 d checked
    circles west gamma F Q Q' qualified.1 qualified'.1 qualified.2.1 qualified'.2.1
    qualified.2.2 qualified'.2.2 r regular
  exact original_injective_on_image (atGamma d gamma)
    (SelectedComponentGame.checked_atGamma d checked gamma)
    Q Q' qualified.2.1 qualified'.2.1 originals

#print axioms Generic.polynomial_eq_of_many_values
#print axioms encoded_eq_on_nonpole
#print axioms grs_eval_eq_of_encoded_eq
#print axioms original_injective_on_image
#print axioms regular_qualified_unique
end
end AspisV8.SelectedOriginalInjectivity

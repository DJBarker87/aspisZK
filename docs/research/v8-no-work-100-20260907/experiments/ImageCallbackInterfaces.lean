import JointImageGame
import AspisFormal.V5FriRelationCandidateBridge
import AspisFormal.V6TranscriptRelationGrammar

/-! Exact algebraic interfaces for the research callback. Not a translated
Rust theorem: parsing, tensor encoder and accumulator refinement stay separate.
No response correspondence equality is assumed in the round identities. -/
set_option autoImplicit false
namespace AspisV8.ImageCallbackInterfaces
open Polynomial Finset
open AspisV8.JointImageGame
open AspisV5RelationSumcheckSoundness
open AspisV5FriRelationCandidateBridge
open AspisV5ComponentCRelationRowLinearity
open AspisV5ComponentCConcreteFoldLinearity
open AspisV6TranscriptRelationGrammar
variable {K : Type*} [Field K] [DecidableEq K]

noncomputable def sent (c : K) (s : RelationRoundParts K) : Fin 7 → K :=
  relationCoefficient (1/4) c s

def imageWeights {n : ℕ} (w : Fin n → K) (i1 i2 i3 : Fin n)
    (tau b c : K) : Fin n → K := fun i => w i +
      (if i=i1 then tau else 0) + (if i=i2 then tau^2*b else 0) -
      (if i=i3 then tau^2*c else 0)

/-- 1023, 1022, 1021 can be substituted without enumerating 1024 cells. -/
theorem image_boundary {n : ℕ} (w v : Fin n → K) (i1 i2 i3 : Fin n)
    (claim tau b c : K) :
    claim - (∑ i, v i * imageWeights w i1 i2 i3 tau b c i) =
      (claim - ∑ i, v i*w i) - tau*v i1 - tau^2*(b*v i2-c*v i3) := by
  simp [imageWeights, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_ite]
  ring

theorem sent_boundary (c : K) (s : RelationRoundParts K) (h4 : (4:K) ≠ 0) :
    relationBoundary (sent c s) = c := by
  simp [relationBoundary, sent, relationCoefficient, reconstructedRelationQuartic]
  field_simp
  <;> ring

theorem game_boundary (v : Fin 7 → K) :
    boundary (relationPolynomial v) = relationBoundary v := by
  simp [boundary, relationPolynomial, relationBoundary, Fin.sum_univ_seven]

/-- Actual compact response minus actual honest convolution, not an
unverified boundary-equality premise in a causal game constructor. -/
theorem compact_error_boundary (n : ℕ) (w v : Fin (4*n) → K)
    (c : K) (s : RelationRoundParts K) (h4 : (4:K) ≠ 0) :
    boundary (relationPolynomial (sent c s) -
      relationPolynomial (polynomialForExtension n w v)) = c - ∑ i, v i*w i := by
  have sub (p r : K[X]) : boundary (p-r) = boundary p - boundary r := by
    simp only [boundary, Polynomial.coeff_sub]; ring
  rw [sub, game_boundary, game_boundary, sent_boundary c s h4,
    relationBoundary_polynomialForExtension n w v h4]

theorem compact_error_degree (n : ℕ) (w v : Fin (4*n) → K)
    (c : K) (s : RelationRoundParts K) :
    (relationPolynomial (sent c s) -
      relationPolynomial (polynomialForExtension n w v)).natDegree ≤ 6 :=
  natDegree_relationPolynomial_sub_le_six _ _

theorem compact_error_eval (n : ℕ) (w v : Fin (4*n) → K)
    (c a : K) (s : RelationRoundParts K) :
    (relationPolynomial (sent c s) -
      relationPolynomial (polynomialForExtension n w v)).eval a =
      relationEvaluate (1/4) c s a - ∑ i,
        coefficientFoldLayer n a v i * dualWeightFoldLayer n a w i := by
  rw [Polynomial.eval_sub, relationPolynomial_polynomialForExtension_eval,
    eval_relationPolynomial]
  rfl

/-- Query injection with the source's PLUS on both claim and weights.
The discrepancy therefore uses MINUS the residual (final - opening), and
starts at rho^1, preserving the earlier discrepancy as constant term. -/
theorem query_injection (n q : ℕ) (v w : Fin n → K)
    (evaluation : Fin q → Fin n → K) (opening : Fin q → K) (c rho : K) :
    (c + ∑ j, rho^(j.val+1)*opening j) -
      (∑ i, v i * (w i + ∑ j, rho^(j.val+1)*evaluation j i)) =
    (c - ∑ i, v i*w i) -
      rho * ∑ j, ((∑ i, v i*evaluation j i) - opening j)*rho^j.val := by
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => v i * (rho ^ (j.val+1) * evaluation j i))]
  simp only [pow_succ]
  have swap (j : Fin q) :
      (∑ i, v i * (rho ^ j.val * rho * evaluation j i)) =
      rho * ((∑ i, v i * evaluation j i) * rho ^ j.val) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  simp_rw [swap, ← Finset.mul_sum]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

/-- Sparse last-block dual propagation. The index decomposition 1021=4*255+1,
1022=4*255+2, 1023=4*255+3; then 255→63→15→3 has slot 3 each time.
This lemma proves the algebra; global index/accumulator refinement is tested. -/
theorem sparse_image_terminal (tau b c a0 a1 a2 a3 : K) :
    (((dualWeightFoldValue a0 ![0,-tau^2*c,tau^2*b,tau]) * a1 / 4) * a2 / 4) * a3 / 4 =
      (a1*a2*a3/256) * (tau*a0 + tau^2*(b*a0^2-c*a0^3)) := by
  have h256 : (256:K) = 4*4*4*4 := by ring
  rw [h256]
  simp [dualWeightFoldValue, div_eq_mul_inv, mul_inv_rev]
  ring

theorem terminal_zero {n : ℕ} (w v : Fin n → K) (c : K)
    (accepted : c = ∑ i, v i*w i) : c - ∑ i, v i*w i = 0 := sub_eq_zero.mpr accepted

#print axioms sent_boundary
#print axioms image_boundary
#print axioms game_boundary
#print axioms compact_error_boundary
#print axioms compact_error_degree
#print axioms compact_error_eval
#print axioms query_injection
#print axioms sparse_image_terminal
#print axioms terminal_zero
end AspisV8.ImageCallbackInterfaces

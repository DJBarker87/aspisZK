import FixedTargetQuerySupport
import ClaimTransport
import AspisFormal.V5ComponentCConcreteFoldLinearity

/-! Symbolic source-map algebra. The verifier's residual is final minus
received, hence the negative of the received-minus-target fold. No agreement,
received polynomiality, or challenge-dependent target is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.TupleQueryTransportCore
open Polynomial
open AspisV5ComponentCConcreteFoldLinearity
open AspisV8.FixedTargetQuerySupport
noncomputable section
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem encode_batch (encoder : V →ₗ[K] (I → K))
    (tuple : Fin 29 → V) (gamma : K) (i : I) :
    encoder (ClaimTransport.batch gamma tuple) i =
      ∑ lane : Fin 29, gamma^lane.val * encoder (tuple lane) i := by
  simp only [ClaimTransport.batch, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

theorem quotient_difference (received interpolant den quotient original : K)
    (nonpole : den ≠ 0) (reconstruction : original = den*quotient+interpolant) :
    (received-interpolant)/den-quotient=(received-original)/den := by
  rw [reconstruction]
  field_simp
  ring

/-- The existing fixed-target polynomial is the literal source circle fold,
including the negative-y orientation of the second pair. -/
theorem foldedPolynomial_source (x y alpha : K) (v : Fin 4 → K)
    (four : (4 : K) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    (foldedPolynomial x y v).eval alpha =
      circleFoldValue alpha (2*x)⁻¹ (2*y)⁻¹ v := by
  rw [foldedPolynomial_eval_literal x y alpha v four hx hy]
  simp only [circleFoldValue, lineFoldValue, pairFoldValue]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A slotwise quotient identity is transported through the actual linear
fold, not through a caller-supplied fold correspondence. -/
theorem residual_fold (x y alpha : K) (received encoded error : Fin 4 → K)
    (four : (4 : K) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (slots : ∀ j, received j-encoded j=error j) :
    circleFoldValue alpha (2*x)⁻¹ (2*y)⁻¹ encoded -
      circleFoldValue alpha (2*x)⁻¹ (2*y)⁻¹ received =
      -(foldedPolynomial x y error).eval alpha := by
  have same : received-encoded=error := funext slots
  have linear := congrArg (circleFoldLinear alpha (2*x)⁻¹ (2*y)⁻¹) same
  rw [map_sub] at linear
  simp only [circleFoldLinear_apply] at linear
  rw [foldedPolynomial_source x y alpha error four hx hy]
  linear_combination -linear

#print axioms encode_batch
#print axioms quotient_difference
#print axioms foldedPolynomial_source
#print axioms residual_fold
end
end AspisV8.TupleQueryTransportCore

import RRChildNormalization
import RRActualFixedParentConvolutionV7

open Polynomial
noncomputable section
namespace RRRootDescent
variable {K : Type*} [Field K]
open RRActualBivariateTaylorBridge

theorem lower_slices_imply_lower_coefficients (Q : (K[X])[X]) (v : Nat)
    (hlower : ∀ k < v, xCoeffSlice Q k = 0) :
    ∀ j k, k < v → (Q.coeff j).coeff k = 0 := by
  intro j k hk
  have h := congrArg (fun p : K[X] => p.coeff j) (hlower k hk)
  simpa only [xCoeffSlice_coeff, coeff_zero] using h

/-- The normalized child's specialization is the very slice whose degree
and multiplicity mass have already been bounded. -/
theorem normalized_specialization_eq_slice (Q : (K[X])[X]) (v : Nat)
    (hlower : ∀ k < v, xCoeffSlice Q k = 0) :
    (stripInnerPower Q v).map (Polynomial.evalRingHom (0 : K)) = xCoeffSlice Q v := by
  ext j
  rw [coeff_map, xCoeffSlice_coeff]
  change ((stripInnerPower Q v).coeff j).eval 0 = (Q.coeff j).coeff v
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simpa only [Nat.add_zero] using
    stripInnerPower_coeff_readback Q v j 0
      (lower_slices_imply_lower_coefficients Q v hlower)

theorem actual_normalized_child_properties (Q : (K[X])[X]) (a : K) (v : Nat)
    (hlower : ∀ k < v, xCoeffSlice (Q.comp (affine a)) k = 0)
    (hnonzero : xCoeffSlice (Q.comp (affine a)) v ≠ 0) :
    let child := stripInnerPower (Q.comp (affine a)) v
    child.map (Polynomial.evalRingHom (0 : K)) = xCoeffSlice (Q.comp (affine a)) v ∧
    child.map (Polynomial.evalRingHom (0 : K)) ≠ 0 ∧
    ∀ g : K[X], child.eval g = 0 ↔ Q.eval (C a + X * g) = 0 := by
  dsimp only
  have hspec := normalized_specialization_eq_slice (Q.comp (affine a)) v hlower
  refine ⟨hspec, ?_, ?_⟩
  · rw [hspec]
    exact hnonzero
  · intro g
    exact stripInnerPower_preserves_roots Q a v g
      (lower_slices_imply_lower_coefficients _ v hlower)

#print axioms lower_slices_imply_lower_coefficients
#print axioms normalized_specialization_eq_slice
#print axioms actual_normalized_child_properties
end RRRootDescent

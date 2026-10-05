import AspisV8R19.R880AugmentedSemanticPolynomial
import AspisV8R19.R881QM31SemanticWeightPolynomial
import AspisV8R19.R877QM31SemanticDeterminant
set_option autoImplicit false
namespace AspisV8R19.R883SelectedQM31AugmentedPolynomial
open MvPolynomial AspisV8R17 AspisV8R15.ExactTowerBase
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R791QM31JointNormalization
open AspisV8R19.R875AugmentedSemanticMatrixHom
open AspisV8R19.R877QM31SemanticDeterminant
open AspisV8R19.R880AugmentedSemanticPolynomial
open AspisV8R19.R881QM31SemanticWeightPolynomial
noncomputable section
local instance : Fact (Nat.Prime 2147483647) := m31PrimeFact
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hh := congrArg (fun x : QM31Exact => x.re.re) h
  change (2 : M31Exact) = 0 at hh
  exact (by decide : (2 : M31Exact) ≠ 0) hh⟩

def selectedPoly := augmentedPolynomial
  (witnessEmbedding R864SemanticKernel.halfSelected)
  (witnessEmbedding (536870912 : ZMod 2147483647)) qm31Weight

theorem selectedPoly_eval (alpha u v kappa tau : QM31Exact) (z : Fin 10 → QM31Exact) :
    (eval (assignment alpha u v kappa tau z)).mapMatrix selectedPoly =
    augmentedMatrix (witnessEmbedding R864SemanticKernel.halfSelected)
      (witnessEmbedding (536870912 : ZMod 2147483647)) alpha u v kappa tau z
      (qm31TupleCoins z) := by
  apply eval_augmentedPolynomial
  intro i
  exact qm31Weight_eval alpha u v kappa tau z i

theorem selectedPoly_det_degree : selectedPoly.det.totalDegree ≤ 14049 :=
  augmentedPolynomial_det_degree _ _ qm31Weight qm31Weight_degree

theorem selectedPoly_witness :
    (eval (assignment (witnessEmbedding 7) (witnessEmbedding 2)
      (witnessEmbedding 3) (witnessEmbedding 5) (witnessEmbedding 0)
      (fun i => witnessEmbedding (R864SemanticKernel.z i)))).mapMatrix selectedPoly =
      qm31Augmented := by
  rw [selectedPoly_eval]
  unfold qm31Augmented
  have hc : qm31TupleCoins (fun i => witnessEmbedding (R864SemanticKernel.z i)) =
      R873SemanticMaskWeightHom.mapCoins witnessEmbedding 10 R864SemanticKernel.semanticZ := by
    rfl
  rw [hc]

theorem selectedPoly_det_ne_zero : selectedPoly.det ≠ 0 := by
  intro hz
  have he := congrArg Matrix.det selectedPoly_witness
  rw [← RingHom.map_det, hz, map_zero] at he
  exact qm31Augmented_det_ne_zero he.symm

#print axioms selectedPoly_eval
#print axioms selectedPoly_det_degree
#print axioms selectedPoly_witness
#print axioms selectedPoly_det_ne_zero
end
end AspisV8R19.R883SelectedQM31AugmentedPolynomial

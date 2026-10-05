import AspisV8R19.R882RootFixedAugmentedPolynomial
import AspisV8R19.R883SelectedQM31AugmentedPolynomial
import AspisV8R19.R879QM31Full223Normalization
set_option autoImplicit false
namespace AspisV8R19.R884SelectedNormalizedSemanticPolynomial
open MvPolynomial AspisV8R17 AspisV8R15.ExactTowerBase
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R791QM31JointNormalization
open AspisV8R19.R875AugmentedSemanticMatrixHom
open AspisV8R19.R879QM31Full223Normalization
open AspisV8R19.R881QM31SemanticWeightPolynomial
open AspisV8R19.R882RootFixedAugmentedPolynomial
noncomputable section
local instance : Fact (Nat.Prime 2147483647) := m31PrimeFact
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hh := congrArg (fun x : QM31Exact => x.re.re) h
  change (2 : M31Exact) = 0 at hh
  exact (by decide : (2 : M31Exact) ≠ 0) hh⟩

def selectedRootPoly (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) := rootFixedAugmentedPolynomial
  (witnessEmbedding R864SemanticKernel.halfSelected)
  (witnessEmbedding (536870912 : ZMod 2147483647)) t ht noneOne qm31Weight

theorem selectedRootPoly_eval (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (alpha u v kappa tau : QM31Exact) (z : Fin 10 → QM31Exact) :
    (eval (assignment alpha u v kappa tau z)).mapMatrix (selectedRootPoly t ht noneOne) =
    normalizedSource223 (witnessEmbedding R864SemanticKernel.halfSelected)
      (witnessEmbedding (536870912 : ZMod 2147483647)) alpha u v kappa tau z
      (qm31TupleCoins z) t ht noneOne := by
  apply eval_rootFixedAugmentedPolynomial
  intro i
  exact qm31Weight_eval alpha u v kappa tau z i

theorem selectedRootPoly_det_degree (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) :
    (selectedRootPoly t ht noneOne).det.totalDegree ≤ 14049 :=
  rootFixedAugmentedPolynomial_det_degree _ _ t ht noneOne qm31Weight qm31Weight_degree

theorem selectedRootPoly_witness (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) :
    (eval (assignment (witnessEmbedding 7) (witnessEmbedding 2)
      (witnessEmbedding 3) (witnessEmbedding 5) (witnessEmbedding 0)
      (fun i => witnessEmbedding (R864SemanticKernel.z i)))).mapMatrix
      (selectedRootPoly t ht noneOne) = normalized223 t ht noneOne := by
  rw [selectedRootPoly_eval]
  have hcoins : qm31TupleCoins (fun i => witnessEmbedding (R864SemanticKernel.z i)) =
      R873SemanticMaskWeightHom.mapCoins witnessEmbedding 10 R864SemanticKernel.semanticZ := by rfl
  rw [hcoins]
  have ha : 1+witnessEmbedding 2*witnessEmbedding 3 = witnessEmbedding 7 := by
    simp only [map_ofNat]; ring
  have hb : witnessEmbedding 2*witnessEmbedding 3-1 = witnessEmbedding 5 := by
    simp only [map_ofNat]; ring
  have hc : -(witnessEmbedding 2+witnessEmbedding 3) = witnessEmbedding (-5) := by
    simp only [map_ofNat, map_neg]; ring
  unfold normalizedSource223 normalized223
  rw [ha, hb, hc]

theorem selectedRootPoly_det_ne_zero (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) : (selectedRootPoly t ht noneOne).det ≠ 0 := by
  intro hz
  have he := congrArg Matrix.det (selectedRootPoly_witness t ht noneOne)
  rw [← RingHom.map_det, hz, map_zero] at he
  exact normalized223_det_ne_zero t ht noneOne he.symm

#print axioms selectedRootPoly_eval
#print axioms selectedRootPoly_det_degree
#print axioms selectedRootPoly_witness
#print axioms selectedRootPoly_det_ne_zero
end
end AspisV8R19.R884SelectedNormalizedSemanticPolynomial

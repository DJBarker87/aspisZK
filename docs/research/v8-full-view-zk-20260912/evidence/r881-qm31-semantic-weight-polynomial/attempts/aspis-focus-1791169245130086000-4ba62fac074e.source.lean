import AspisV8R19.R876SemanticWeightPolynomial
import AspisV8R19.R791QM31JointNormalization
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
namespace AspisV8R19.R881QM31SemanticWeightPolynomial
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R876SemanticWeightPolynomial
open AspisV8R19.R791QM31JointNormalization
open AspisV8R15.ExactTowerBase
open AspisV8R17
open MvPolynomial
noncomputable section

abbrev M := ZMod 2147483647
abbrev PolyM := JointPoly M
abbrev PolyQ := JointPoly AspisV8R15.ExactTowerBase.QM31Exact

def qm31Weight (i : Fin 271) : PolyQ :=
  MvPolynomial.map witnessEmbedding (semanticWeightPoly i)

def qm31TupleCoins (z : Fin 10 → AspisV8R15.ExactTowerBase.QM31Exact) :
    AspisV8R17.RoundCoins AspisV8R15.ExactTowerBase.QM31Exact 10 :=
  (z 0, (z 1, (z 2, (z 3, (z 4, (z 5, (z 6, (z 7, (z 8, (z 9, PUnit.unit))))))))))

def qm31Assignment (alpha u v kappa tau : AspisV8R15.ExactTowerBase.QM31Exact) (z : Fin 10 → AspisV8R15.ExactTowerBase.QM31Exact) :
    Fin 15 → AspisV8R15.ExactTowerBase.QM31Exact := assignment alpha u v kappa tau z

def qm31Eval (alpha u v kappa tau : AspisV8R15.ExactTowerBase.QM31Exact) (z : Fin 10 → AspisV8R15.ExactTowerBase.QM31Exact) : PolyQ →+* AspisV8R15.ExactTowerBase.QM31Exact :=
  MvPolynomial.eval₂Hom (RingHom.id AspisV8R15.ExactTowerBase.QM31Exact) (qm31Assignment alpha u v kappa tau z)

theorem qm31Weight_degree (i : Fin 271) :
    (qm31Weight i).totalDegree ≤ 27 := by
  change MvPolynomial.totalDegree
      (MvPolynomial.map witnessEmbedding (semanticWeightPoly i)) ≤ 27
  calc
    MvPolynomial.totalDegree (MvPolynomial.map witnessEmbedding (semanticWeightPoly i)) ≤
        MvPolynomial.totalDegree (semanticWeightPoly i) :=
      MvPolynomial.totalDegree_le_of_support_subset
        (p := MvPolynomial.map witnessEmbedding (semanticWeightPoly i))
        (q := semanticWeightPoly i)
        (MvPolynomial.support_map_subset witnessEmbedding (semanticWeightPoly i))
    _ ≤ 27 := semanticWeightPoly_degree i

theorem qm31Weight_eval (alpha u v kappa tau : AspisV8R15.ExactTowerBase.QM31Exact)
    (z : Fin 10 → AspisV8R15.ExactTowerBase.QM31Exact) (i : Fin 271) :
    qm31Eval alpha u v kappa tau z (qm31Weight i) =
      maskWeights271 (witnessEmbedding (1073741824 : M)) (qm31TupleCoins z) i := by
  change MvPolynomial.eval₂ (RingHom.id AspisV8R15.ExactTowerBase.QM31Exact)
      (qm31Assignment alpha u v kappa tau z)
      (MvPolynomial.map witnessEmbedding (semanticWeightPoly i)) = _
  rw [MvPolynomial.eval₂_map]
  simp only [RingHom.id_comp]
  have h := semanticWeightPoly_eval_at witnessEmbedding alpha u v kappa tau z i
  change MvPolynomial.eval₂Hom witnessEmbedding
      (assignment alpha u v kappa tau z) (semanticWeightPoly i) = _ at h
  simpa [qm31Assignment] using h

#print axioms qm31Weight_degree
#print axioms qm31Weight_eval
end
end AspisV8R19.R881QM31SemanticWeightPolynomial

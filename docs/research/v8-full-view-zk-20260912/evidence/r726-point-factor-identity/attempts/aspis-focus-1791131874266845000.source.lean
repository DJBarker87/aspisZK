import AspisV8R19.SourceStatementPoints
import AspisV8R17.SourceOriginalWeights
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R726PointFactorIdentity
open AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open scoped BigOperators
variable {F : Type*} [CommRing F]

lemma point_factor_identity (z : Fin 10 → F) (r : Nat)
    (h3 : (r >>> 3) &&& 1 = 1) (h2 : (r >>> 2) &&& 1 = 1) :
    z 6 * z 7 * sourcePointBasis (points z 2) r =
      (1-z 6)*(1-z 7)*sourcePointBasis (points z 0) r := by
  rw [points_eq,points_eq]
  unfold sourcePointBasis sourceMultilinearFactors
  simp only [List.prod_ofFn,ResidualModel.point]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ]
  -- The two specified bits select the flipped coordinates 6 and 7.
  simp [h3,h2]
  ring

#print axioms point_factor_identity
end AspisV8R19.R726PointFactorIdentity

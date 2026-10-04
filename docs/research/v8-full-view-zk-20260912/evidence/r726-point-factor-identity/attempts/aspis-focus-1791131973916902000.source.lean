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
  classical
  rw [points_eq,points_eq]
  unfold sourcePointBasis sourceMultilinearFactors
  simp only [List.prod_ofFn]
  have split_prod (f : Fin 10 → F) :
      (∏ i : Fin 10, f i) = f 6 * f 7 * ∏ i ∈ (Finset.univ.erase 6).erase 7, f i := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (6 : Fin 10))]
    rw [← Finset.prod_erase_mul _ _ (by simp : (7 : Fin 10) ∈ Finset.univ.erase 6)]
    ring
  sorry

#print axioms point_factor_identity
end AspisV8R19.R726PointFactorIdentity

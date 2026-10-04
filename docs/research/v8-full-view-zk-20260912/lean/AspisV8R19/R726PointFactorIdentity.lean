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
  rw [split_prod, split_prod]
  let s : Finset (Fin 10) := (Finset.univ.erase 6).erase 7
  have hrest :
      (∏ i ∈ s, if (r >>> (9-i.val)) &&& 1 = 0 then
        1-ResidualModel.point z (2:Fin 3).val i else ResidualModel.point z (2:Fin 3).val i) =
      (∏ i ∈ s, if (r >>> (9-i.val)) &&& 1 = 0 then
        1-ResidualModel.point z (0:Fin 3).val i else ResidualModel.point z (0:Fin 3).val i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hi7 : i ≠ 7 := (Finset.mem_erase.mp hi).1
    have hi6 : i ≠ 6 := (Finset.mem_erase.mp ((Finset.mem_erase.mp hi).2)).1
    have hiv6 : i.val ≠ 6 := by
      intro h
      apply hi6
      exact Fin.ext h
    have hiv7 : i.val ≠ 7 := by
      intro h
      apply hi7
      exact Fin.ext h
    simp [ResidualModel.point,hiv6,hiv7]
  dsimp [s] at hrest
  have h6 : r >>> 3 % 2 = 1 := by
    simpa only [Nat.and_one_is_mod] using h3
  have h7 : r >>> 2 % 2 = 1 := by
    simpa only [Nat.and_one_is_mod] using h2
  norm_num only
  have hrest' :
      (∏ i ∈ (Finset.univ.erase 6).erase 7,
        if (r >>> (9-i.val)) &&& 1 = 0 then
          1-ResidualModel.point z (2:Fin 3).val i else ResidualModel.point z (2:Fin 3).val i) =
      (∏ i ∈ (Finset.univ.erase 6).erase 7,
        if (r >>> (9-i.val)) &&& 1 = 0 then
          1-ResidualModel.point z (0:Fin 3).val i else ResidualModel.point z (0:Fin 3).val i) := by
    exact hrest
  rw [hrest']
  simp [Nat.and_one_is_mod, ResidualModel.point, h6, h7]
  ring

#print axioms point_factor_identity
end AspisV8R19.R726PointFactorIdentity

import AspisV8R19.R887Full223CombinationObservation
import AspisV8R19.R889Full223KernelProperties
import AspisV8R19.R852FullOrdinaryCoefficientBoundary
import AspisV8R19.R370KernelEvaluation

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R890Full223DeterminantFourthRoot

open AspisV8R19.R887Full223CombinationObservation
open AspisV8R19.R889Full223KernelProperties
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R852FullOrdinaryCoefficientBoundary
open AspisR19.R370KernelEvaluation
open AspisV8R17 AspisR19
open scoped BigOperators

noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem determinant_excludes_fourth_root
    (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (hdet : (normalizedSource223 half quarter alpha u v kappa tau z (fun _ => 0) t ht noneOne).det ≠ 0) :
    alpha^4 ≠ 1 := by
  intro ha4
  let target : R887Full223CombinationObservation.Obs ⊕ Unit → F
    | .inl (.inl _) => 0
    | .inl (.inr (.inl _)) => 0
    | .inl (.inr (.inr j)) => if j.val = 0 then 1 else 0
    | .inr _ => 0
  obtain ⟨x,hobs⟩ :=
    combination223_surjective half quarter alpha u v kappa tau z (fun _ => 0)
      t ht noneOne hdet target
  let q : Index256 → F := combination223 alpha t ht noneOne x
  have hfold := combination223_firstFold alpha t ht noneOne x
  have hTop := flatten_combination223_top alpha t ht noneOne x
  have hpoint0 : sourcePointFunctional (SourceStatementPoints.points z 0)
      (rawMask half (1+u*v) (u*v-1) (-(u+v)) q) = 0 := by
    have h := hobs (.inl (.inr (.inl (0 : Fin 3))))
    simpa [q, target, rawObservation] using h
  have hpoint1 : sourcePointFunctional (SourceStatementPoints.points z 1)
      (rawMask half (1+u*v) (u*v-1) (-(u+v)) q) = 0 := by
    have h := hobs (.inl (.inr (.inl (1 : Fin 3))))
    simpa [q, target, rawObservation] using h
  have hpoint2 : sourcePointFunctional (SourceStatementPoints.points z 2)
      (rawMask half (1+u*v) (u*v-1) (-(u+v)) q) = 0 := by
    have h := hobs (.inl (.inr (.inl (2 : Fin 3))))
    simpa [q, target, rawObservation] using h
  have hrel1 : rawRelation half quarter (1+u*v) (u*v-1) (-(u+v))
      kappa tau z q 1 = 1 := by
    have h := hobs (.inl (.inr (.inr (0 : Fin 5))))
    simpa [q, target, rawObservation, relationIndex] using h
  have hrel2 : rawRelation half quarter (1+u*v) (u*v-1) (-(u+v))
      kappa tau z q 2 = 0 := by
    have h := hobs (.inl (.inr (.inr (1 : Fin 5))))
    simpa [q, target, rawObservation, relationIndex] using h
  have hrel3 : rawRelation half quarter (1+u*v) (u*v-1) (-(u+v))
      kappa tau z q 3 = 0 := by
    have h := hobs (.inl (.inr (.inr (2 : Fin 5))))
    simpa [q, target, rawObservation, relationIndex] using h
  have hrel5 : rawRelation half quarter (1+u*v) (u*v-1) (-(u+v))
      kappa tau z q 5 = 0 := by
    have h := hobs (.inl (.inr (.inr (3 : Fin 5))))
    simpa [q, target, rawObservation, relationIndex] using h
  have hrel6 : rawRelation half quarter (1+u*v) (u*v-1) (-(u+v))
      kappa tau z q 6 = 0 := by
    have h := hobs (.inl (.inr (.inr (4 : Fin 5))))
    simpa [q, target, rawObservation, relationIndex] using h
  have htopRaw : ∀ r : Nat, 1020 ≤ r → rawFlatten q r = 0 := by
    intro r hr
    rw [rawFlatten_eq_flattenFull]
    exact hTop r hr
  have hboundary :
      rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q 0 +
      rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q 4 = 0 := by
    rw [ordinary_coefficient_boundary_of_top_zero
      half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q htopRaw]
    simp only [hpoint0, hpoint1, hpoint2, mul_zero, zero_add]
  let w : Fin 256 × Fin 4 → F := fun i =>
    rawOrdinaryWeight half (1+u*v) (u*v-1) (-(u+v)) kappa tau z
      (4*i.1.val+i.2.val)
  have hkernel : kernelEval 256 quarter alpha q w = 0 := by
    apply kernel_eval_zero_of_first_fold 256 quarter alpha q w
    intro d
    exact hfold d
  have hsum :
      (∑ k : Fin 7,
        rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q k.val * alpha^k.val) = 0 := by
    change (∑ k : Fin 7,
      rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q k.val * alpha^k.val) = 0 at hkernel
    exact hkernel
  have hpoly :
      rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q 0 +
        alpha + alpha^4 *
          rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q 4 = 0 := by
    have hh := hsum
    repeat rw [Fin.sum_univ_succ] at hh
    simp only [Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ] at hh
    rw [hrel1, hrel2, hrel3, hrel5, hrel6] at hh
    simp only [pow_zero, pow_one, mul_one, zero_mul, zero_add, add_zero] at hh
    linear_combination hh
  rw [ha4] at hpoly
  have halpha : alpha = 0 := by
    linear_combination hpoly - hboundary
  rw [halpha] at ha4
  norm_num at ha4

#print axioms determinant_excludes_fourth_root

end
end AspisV8R19.R890Full223DeterminantFourthRoot

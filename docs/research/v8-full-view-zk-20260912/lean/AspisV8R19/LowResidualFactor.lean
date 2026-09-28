/- Low-block locality and query-factor determinant. Source weight equality and
   natural-basis transformation remain separate refinement obligations. -/
import AspisV8R19.BetaUniformCorrection
import AspisV8R17.MinorDegree

namespace AspisR19.LowResidualFactor
open AspisR19.BetaUniformCorrection MvPolynomial
variable {F : Type*} [CommRing F]
noncomputable section

abbrev Index := Fin 256 × Fin 4

theorem low_coefficient (q : Index → F) (w v : Index → F)
    (quarter : F) (k : Nat)
    (hq : ∀ i, 106 ≤ 4*i.1.val+i.2.val → q i=0)
    (hw : ∀ j, 4*j.1.val+j.2.val<108 → w j=v j) :
    coefficient (sourceKernel 256 k quarter) q w =
      coefficient (sourceKernel 256 k quarter) q v := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : 106 ≤ 4*i.1.val+i.2.val
  · rw [hq i hi]; simp
  · by_cases hc : i.1=j.1
    · have hj : 4*j.1.val+j.2.val<108 := by
        have := i.2.isLt
        have := j.2.isLt
        have hv := congrArg Fin.val hc
        omega
      rw [hw j hj]
    · simp [sourceKernel,hc]

theorem point_reduction (q : Index → F) (w e₀ e₁ e₂ : Index → F)
    (quarter κ : F) (k : Nat)
    (hq : ∀ i, 106 ≤ 4*i.1.val+i.2.val → q i=0)
    (hw : ∀ j, 4*j.1.val+j.2.val<108 →
      w j=κ*e₀ j+κ^2*e₁ j+κ^3*e₂ j) :
    coefficient (sourceKernel 256 k quarter) q w =
      κ*coefficient (sourceKernel 256 k quarter) q e₀+
      κ^2*coefficient (sourceKernel 256 k quarter) q e₁+
      κ^3*coefficient (sourceKernel 256 k quarter) q e₂ := by
  rw [low_coefficient q w (fun j => κ*e₀ j+κ^2*e₁ j+κ^3*e₂ j) quarter k hq hw]
  have h := coefficient_right (sourceKernel 256 k quarter) q
    (fun j => κ*e₀ j+κ^2*e₁ j) e₂ 1 (κ^3)
  simp only [one_mul] at h
  rw [h,coefficient_right]

/- a is the coefficient tensor of the 13x13 factor-basis minor, with all
   non-query challenges fixed. This does not assert a source oracle law. -/
def entry (a : Fin 13 → Fin 13 → Fin 23 → F) (i j : Fin 13) :
    MvPolynomial (Fin 23) F := ∑ d, C (a i j d)*X d

theorem entry_eval (a : Fin 13 → Fin 13 → Fin 23 → F)
    (p : Fin 23 → F) (i j : Fin 13) :
    eval p (entry a i j) = ∑ d, a i j d*p d := by
  simp [entry]

theorem entry_degree [Nontrivial F] (a : Fin 13 → Fin 13 → Fin 23 → F) (i j : Fin 13) :
    (entry a i j).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro d _
  exact (totalDegree_mul _ _).trans (by simp [totalDegree_X])

theorem determinant_degree [Nontrivial F] (a : Fin 13 → Fin 13 → Fin 23 → F) :
    (Matrix.det (entry a)).totalDegree ≤ 13 := by
  simpa using AspisV8R17.minor_totalDegree (entry a) 1 (entry_degree a)

theorem determinant_eval (a : Fin 13 → Fin 13 → Fin 23 → F)
    (p : Fin 23 → F) :
    eval p (Matrix.det (entry a)) =
      Matrix.det (fun i j => ∑ d, a i j d*p d) := by
  rw [(eval p).map_det]
  congr 1
  ext i j
  exact entry_eval a p i j

theorem basis_change_det (D U : Matrix (Fin 13) (Fin 13) F) (half : F)
    (hU : U.det=half^269) : (D*U).det=D.det*half^269 := by
  rw [Matrix.det_mul,hU]

theorem basis_change_nonzero {K : Type*} [Field K]
    (D U : Matrix (Fin 13) (Fin 13) K) (half : K)
    (hhalf : half≠0) (hU : U.det=half^269) :
    (D*U).det≠0 ↔ D.det≠0 := by
  rw [basis_change_det D U half hU]
  simp [hhalf]

#print axioms low_coefficient
#print axioms point_reduction
#print axioms entry_eval
#print axioms entry_degree
#print axioms determinant_degree
#print axioms determinant_eval
#print axioms basis_change_det
#print axioms basis_change_nonzero
end
end AspisR19.LowResidualFactor

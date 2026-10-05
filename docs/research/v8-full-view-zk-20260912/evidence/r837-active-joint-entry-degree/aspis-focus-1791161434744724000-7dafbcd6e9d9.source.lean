import AspisV8R19.R745JointObservationPolynomial
import AspisV8R19.R746SelectedJointMinor
import AspisV8R17.MinorDegree
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R837ActiveJointEntryDegree
open MvPolynomial
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R746SelectedJointMinor
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem polynomialABC_totalDegree_le (l : Fin 3) :
    (polynomialABC (F := F) l).totalDegree ≤ 2 := by
  have hmul : ((X (1 : Fin 15) * X 2 : JointPoly F)).totalDegree ≤ 2 := by
    simpa [pU, pV] using totalDegree_mul (X (1 : Fin 15) : JointPoly F) (X 2)
  unfold polynomialABC
  fin_cases l
  · exact (totalDegree_add _ _).trans (max_le (by simp) hmul)
  · exact (totalDegree_sub _ _).trans (max_le hmul (by simp))
  · rw [totalDegree_neg]
    exact (totalDegree_add (X (1 : Fin 15) : JointPoly F) (X 2)).trans (by simp)

theorem active_polynomialEntry_totalDegree_le (half quarter : F) (d : Fin 255)
    (s : Fin 3) (j : J) :
    (polynomialEntry half quarter d s (.inl j)).totalDegree ≤ 5 := by
  simp only [polynomialEntry]
  apply totalDegree_finsetSum_le
  intro l hl
  have hpow : (pAlpha ^ (s.val + 1) : JointPoly F).totalDegree ≤ s.val + 1 := by
    simpa [pAlpha] using
      (totalDegree_pow (X (0 : Fin 15) : JointPoly F) (s.val + 1))
  have hk : s.val + 1 ≤ 3 := by omega
  have hshift :
      (pAlpha ^ (s.val + 1) *
        C (sourceBasisConstants half (sdiff d)
          (R707FullActiveDeterminant.rowCode j) l) : JointPoly F).totalDegree ≤ 3 := by
    exact (totalDegree_mul _ _).trans (by simpa using hpow.trans hk)
  have hconstant :
      (C (sourceBasisConstants half (qdiff d s)
        (R707FullActiveDeterminant.rowCode j) l) : JointPoly F).totalDegree ≤ 0 := by
    simp
  have hbracket :
      (C (sourceBasisConstants half (qdiff d s)
          (R707FullActiveDeterminant.rowCode j) l) -
        pAlpha ^ (s.val + 1) *
          C (sourceBasisConstants half (sdiff d)
            (R707FullActiveDeterminant.rowCode j) l)).totalDegree ≤ 3 := by
    exact (totalDegree_sub _ _).trans
      (max_le (hconstant.trans (by omega)) hshift)
  exact (totalDegree_mul _ _).trans
    (Nat.add_le_add (polynomialABC_totalDegree_le l) hbracket)

#print axioms polynomialABC_totalDegree_le
#print axioms active_polynomialEntry_totalDegree_le
end
end AspisV8R19.R837ActiveJointEntryDegree

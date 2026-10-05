import Mathlib.Algebra.MvPolynomial.CommRing
import AspisV8R19.R745JointObservationPolynomial
import AspisV8R19.R836StatementPointDegree
import AspisV8R19.R838SourceWeightDegree

/-! Uniform point-row degree bound for the actual sparse joint polynomial. -/
set_option autoImplicit false
namespace AspisV8R19.R840JointPointRowDegree
open MvPolynomial
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R836StatementPointDegree
open AspisV8R19.R838SourceWeightDegree
noncomputable section

variable {F : Type*} [Field F]

theorem pointWeight_statement_degree (half : F) (p : Fin 3) (i : Nat) :
    (pointWeight (F := JointPoly F) (C half)
      (1 + pU*pV) (pU*pV - 1) (-(pU+pV))
      (SourceStatementPoints.points (pZ (F := F)) p) i).totalDegree ≤ 57 := by
  let w : Fin 1024 → JointPoly F := fun j =>
    AspisV8R16.transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
      (fun k => sourcePointBasis (SourceStatementPoints.points (pZ (F := F)) p) k.val) j
  have hb (j : Fin 1024) :
      (sourcePointBasis (SourceStatementPoints.points (pZ (F := F)) p) j.val).totalDegree ≤ 55 :=
    source_point_basis_degree (F := F) p j.val
  have hwj (j : Fin 1024) : (w j).totalDegree ≤ 55 := by
    dsimp [w]
    unfold AspisV8R16.transportDual
    split
    · exact (totalDegree_sub _ _).trans (max_le (hb _) (hb _))
    · exact hb _
  have hw (n : Nat) : (extendFin1024 w n).totalDegree ≤ 55 := by
    unfold extendFin1024
    split
    · exact hwj _
    · simp
  have ha : ((1 + pU*pV : JointPoly F)).totalDegree ≤ 2 := by
    exact (totalDegree_add _ _).trans (max_le (by simp) (by
      simpa [pU, pV] using totalDegree_mul (X (1 : Fin 15) : JointPoly F) (X 2)))
  have hbc : ((pU*pV - 1 : JointPoly F)).totalDegree ≤ 2 := by
    exact (totalDegree_sub _ _).trans (max_le (by
      simpa [pU, pV] using totalDegree_mul (X (1 : Fin 15) : JointPoly F) (X 2)) (by simp))
  have hc : ((-(pU+pV) : JointPoly F)).totalDegree ≤ 2 := by
    rw [totalDegree_neg]
    exact (totalDegree_add (X (1 : Fin 15) : JointPoly F) (X 2)).trans (by simp)
  simpa [pointWeight, w] using
    (sourceChordTranspose_degree (F := F) half (extendFin1024 w)
      (1+pU*pV) (pU*pV-1) (-(pU+pV)) 55 2 hw ha hbc hc i)

theorem point_row_polynomialEntry_totalDegree_le (half quarter : F)
    (d : Fin 255) (s : Fin 3) (p : Fin 3) :
    (polynomialEntry half quarter d s (.inr (.inl p))).totalDegree ≤ 60 := by
  simp only [polynomialEntry, sparseObservation]
  have hpow : ((pAlpha : JointPoly F)^(s.val+1)).totalDegree ≤ 3 := by
    have hp : ((pAlpha : JointPoly F)^(s.val+1)).totalDegree ≤ s.val+1 := by
      simpa [pAlpha] using totalDegree_pow (X (0 : Fin 15) : JointPoly F) (s.val+1)
    exact hp.trans (by omega)
  have hweight (n : Nat) :
      (pointWeight (F := JointPoly F) (C half) (1+pU*pV) (pU*pV-1) (-(pU+pV))
        (SourceStatementPoints.points (pZ (F := F)) p) n).totalDegree ≤ 57 :=
    pointWeight_statement_degree (F := F) half p n
  have hproduct (n : Nat) :
      ((pAlpha : JointPoly F)^(s.val+1) *
        pointWeight (F := JointPoly F) (C half) (1+pU*pV) (pU*pV-1) (-(pU+pV))
          (SourceStatementPoints.points (pZ (F := F)) p) n).totalDegree ≤ 60 := by
    exact (totalDegree_mul _ _).trans (Nat.add_le_add hpow (hweight n))
  have hleft :
      (pointWeight (F := JointPoly F) (C half) (1+pU*pV) (pU*pV-1) (-(pU+pV))
          (SourceStatementPoints.points (pZ (F := F)) p) (4*d.val+s.val+1) -
        pAlpha^(s.val+1) * pointWeight (F := JointPoly F) (C half)
          (1+pU*pV) (pU*pV-1) (-(pU+pV))
          (SourceStatementPoints.points (pZ (F := F)) p) (4*d.val)).totalDegree ≤ 60 := by
      exact (totalDegree_sub _ _).trans (max_le ((hweight _).trans (by omega)) (hproduct _))
  have hright :
      (pointWeight (F := JointPoly F) (C half) (1+pU*pV) (pU*pV-1) (-(pU+pV))
          (SourceStatementPoints.points (pZ (F := F)) p) (s.val+1) -
        pAlpha^(s.val+1) * pointWeight (F := JointPoly F) (C half)
          (1+pU*pV) (pU*pV-1) (-(pU+pV))
          (SourceStatementPoints.points (pZ (F := F)) p) 0).totalDegree ≤ 60 := by
      exact (totalDegree_sub _ _).trans (max_le ((hweight _).trans (by omega)) (hproduct _))
  have hfirst :
      (pointWeight (F := JointPoly F) (C half) (1+pU*pV) (pU*pV-1) (-(pU+pV))
          (SourceStatementPoints.points (pZ (F := F)) p) (4*d.val+s.val+1) -
        pAlpha^(s.val+1) * pointWeight (F := JointPoly F) (C half)
          (1+pU*pV) (pU*pV-1) (-(pU+pV))
          (SourceStatementPoints.points (pZ (F := F)) p) (4*d.val) -
        (pointWeight (F := JointPoly F) (C half) (1+pU*pV) (pU*pV-1) (-(pU+pV))
          (SourceStatementPoints.points (pZ (F := F)) p) (s.val+1) -
        pAlpha^(s.val+1) * pointWeight (F := JointPoly F) (C half)
          (1+pU*pV) (pU*pV-1) (-(pU+pV))
          (SourceStatementPoints.points (pZ (F := F)) p) 0)).totalDegree ≤ 60 := by
      exact (totalDegree_sub _ _).trans (max_le hleft hright)
  exact hfirst

#print axioms pointWeight_statement_degree
#print axioms point_row_polynomialEntry_totalDegree_le
end
end AspisV8R19.R840JointPointRowDegree

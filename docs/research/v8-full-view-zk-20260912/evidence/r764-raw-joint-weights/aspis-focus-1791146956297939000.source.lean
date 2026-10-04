import AspisV8R19.R758NormalizedLowRepair
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R665FullSourceP2Boundary

namespace AspisV8R19.R764RawJointWeights
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R665FullSourceP2Boundary
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def jointWeight (half quarter a b c kappa tau : F) (z : Fin 10 → F)
    (row : ObservationRow) (i : Index256) : F :=
  match row with
  | .inl j => sourceChordTranspose half (unitVector (R707FullActiveDeterminant.rowCode j))
      a b c (4*i.1.val+i.2.val)
  | .inr (.inl p) => pointWeight half a b c (SourceStatementPoints.points z p)
      (4*i.1.val+i.2.val)
  | .inr (.inr k) => rowWeight 256 (relationIndex k) quarter
      (fun i => rawOrdinaryWeight half a b c kappa tau z (4*i.1.val+i.2.val)) i.1 i.2

theorem rowCode_lt (j : R738JointObservationModel.J) :
    R707FullActiveDeterminant.rowCode j < 1024 := by
  rcases j with i | u
  · have h := i.val.isLt
    change i.val.val < 1024
    omega
  · change 1022 < 1024
    decide

/-- All raw joint rows retain their exact full 256-by-four source weights. -/
theorem rawObservation_weighted (half quarter a b c kappa tau : F) (z : Fin 10 → F)
    (q : Index256 → F) (row : ObservationRow) :
    rawObservation half quarter a b c kappa tau z q row =
      ∑ d : Fin 256, ∑ s : Fin 4, q (d,s) * jointWeight half quarter a b c kappa tau z row (d,s) := by
  rcases row with j | ⟨p | k⟩
  · have h := source_chord_transpose_pairing half (rawFlatten q)
      (unitVector (R707FullActiveDeterminant.rowCode j)) a b c
    have hleft : rangeDot 1024 (unitVector (R707FullActiveDeterminant.rowCode j))
        (sourceChord half (rawFlatten q) a b c) =
        sourceChord half (rawFlatten q) a b c (R707FullActiveDeterminant.rowCode j) := by
      rw [rangeDot_comm]
      exact rangeDot_unitVector 1024 _ (rowCode_lt j) _
    rw [hleft] at h
    change sourceChord half (rawFlatten q) a b c (R707FullActiveDeterminant.rowCode j) = _
    rw [h]
    change rangeDot 1024 _ (AspisV8R19.R662FullIndexedMaskPreservation.flattenFull q) = _
    exact full_flatten_pairing q _
  · change sourcePointFunctional (SourceStatementPoints.points z p)
      (inverseTransport TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
        (fun j => sourceChord half (rawFlatten q) a b c j.val)) = _
    rw [point_transport_pairing]
    change rangeDot 1024 _ (AspisV8R19.R662FullIndexedMaskPreservation.flattenFull q) = _
    exact full_flatten_pairing q _
  · change BetaUniformCorrection.coefficient
      (BetaUniformCorrection.sourceKernel 256 (relationIndex k) quarter) q
      (fun i => rawOrdinaryWeight half a b c kappa tau z (4*i.1.val+i.2.val)) = _
    rw [FullCoefficientBoundary.coefficient_blocks]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro s _
    change (∑ t : Fin 4, (if s.val+(4-t.val)%4=relationIndex k then quarter else 0) *
      q (d,s) * rawOrdinaryWeight half a b c kappa tau z (4*d.val+t.val)) =
      q (d,s) * rowWeight 256 (relationIndex k) quarter
        (fun i => rawOrdinaryWeight half a b c kappa tau z (4*i.1.val+i.2.val)) d s
    rw [rowWeight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring

#print axioms rowCode_lt
#print axioms rawObservation_weighted
end
end AspisV8R19.R764RawJointWeights

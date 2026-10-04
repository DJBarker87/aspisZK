import AspisV8R19.R738JointObservationModel
import AspisV8R19.R740SparsePointObservation
import AspisV8R19.R741SparseCoefficientObservation

/-! Entrywise binding of the finite indexed sparse directions to the R738
ordinary joint-observation model.  No rank or source-execution fact is used. -/
set_option autoImplicit false
namespace AspisV8R19.R743JointSparseEntryBinding
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R741SparseCoefficientObservation
open scoped BigOperators
noncomputable section
variable {F : Type*} [CommRing F]

abbrev Index256 := R738JointObservationModel.Index256
abbrev ObservationRow := R738JointObservationModel.ObservationRow

def indexedDirection (alpha : F) (d : Fin 255) (s : Fin 3) : Index256 → F :=
  fun i => indexedPair alpha (cast255 d) s i - indexedPair alpha 0 s i

theorem rawFlatten_indexedDirection (alpha : F) (d : Fin 255) (s : Fin 3) :
    rawFlatten (indexedDirection alpha d s) = direction alpha d s := by
  funext r
  unfold rawFlatten
  split
  · let i : Fin 256 × Fin 4 :=
      (⟨r / 4, by omega⟩, ⟨r % 4, Nat.mod_lt _ (by decide)⟩)
    change indexedPair alpha (cast255 d) s i - indexedPair alpha 0 s i = _
    rw [indexedPair_qPair alpha d s i, indexedPair_qPair alpha 0 s i]
    unfold direction
    congr 2 <;> omega
  · unfold direction qPair
    have h1 : r ≠ 4*d.val+s.val+1 := by omega
    have h2 : r ≠ 4*d.val := by omega
    have h3 : r ≠ s.val+1 := by omega
    have h4 : r ≠ 0 := by omega
    simp [unitVector, h1, h2, h3, h4]

def sparseObservation (half quarter a b c kappa tau alpha : F) (z : Fin 10 → F)
    (d : Fin 255) (s : Fin 3) : ObservationRow → F
  | .inl j => sourceChord half (direction alpha d s) a b c
      (R707FullActiveDeterminant.rowCode j)
  | .inr (.inl p) =>
      (pointWeight half a b c (SourceStatementPoints.points z p) (4*d.val+s.val+1) -
        alpha^(s.val+1) * pointWeight half a b c (SourceStatementPoints.points z p) (4*d.val)) -
      (pointWeight half a b c (SourceStatementPoints.points z p) (s.val+1) -
        alpha^(s.val+1) * pointWeight half a b c (SourceStatementPoints.points z p) 0)
  | .inr (.inr k) =>
      (rowWeight 256 (relationIndex k) quarter
          (fun i => rawOrdinaryWeight half a b c kappa tau z (4*i.1.val+i.2.val))
          (cast255 d) ⟨s.val+1, by omega⟩ -
        alpha^(s.val+1) * rowWeight 256 (relationIndex k) quarter
          (fun i => rawOrdinaryWeight half a b c kappa tau z (4*i.1.val+i.2.val))
          (cast255 d) 0) -
      (rowWeight 256 (relationIndex k) quarter
          (fun i => rawOrdinaryWeight half a b c kappa tau z (4*i.1.val+i.2.val))
          0 ⟨s.val+1, by omega⟩ -
        alpha^(s.val+1) * rowWeight 256 (relationIndex k) quarter
          (fun i => rawOrdinaryWeight half a b c kappa tau z (4*i.1.val+i.2.val)) 0 0)

theorem rawObservation_indexedDirection (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (d : Fin 255) (s : Fin 3) :
    rawObservation half quarter a b c kappa tau z (indexedDirection alpha d s) =
      sparseObservation half quarter a b c kappa tau alpha z d s := by
  funext row
  rcases row with j | ⟨p | k⟩
  · simp only [rawObservation, sparseObservation]
    rw [rawFlatten_indexedDirection]
  · simp only [rawObservation, sparseObservation]
    unfold rawMask
    rw [rawFlatten_indexedDirection]
    exact direction_point_observation half a b c alpha
      (SourceStatementPoints.points z p) d s
  · simp only [rawObservation, sparseObservation, rawRelation]
    exact coefficient_direction alpha (relationIndex k) quarter
      (fun i => rawOrdinaryWeight half a b c kappa tau z (4*i.1.val+i.2.val))
      (cast255 d) s

#print axioms rawFlatten_indexedDirection
#print axioms rawObservation_indexedDirection
end
end AspisV8R19.R743JointSparseEntryBinding

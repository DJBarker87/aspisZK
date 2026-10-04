import AspisV8R19.R785SourceTransposeLinear
import AspisV8R17.CompactTransport
import AspisV8R19.R738JointObservationModel

/-! Function-level decomposition of the selected ordinary source weights. -/
set_option autoImplicit false
namespace AspisV8R19.R788OrdinaryPointDecomposition

open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R17.CompactTransport
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R785SourceTransposeLinear
noncomputable section

variable {F : Type*} [CommRing F]

def wp (z : Fin 10 → F) (p : Fin 3) : Nat → F :=
  extendFin1024 (transportDual inactive 1023 order
    (fun j => sourcePointBasis (SourceStatementPoints.points z p) j.val))

def marker : Nat → F :=
  extendFin1024 (pivotMarker (K := F) (1023 : Fin 1024) order)

theorem pivot_mem_inactive : (1023 : Fin 1024) ∈ inactive := by decide

theorem extend_linear (x y : F) (u v : Fin 1024 → F) (r : Nat) :
    extendFin1024 (fun i => x * u i + y * v i) r =
      x * extendFin1024 u r + y * extendFin1024 v r := by
  unfold extendFin1024
  split <;> simp <;> ring

theorem original_false_decomposition (z : Fin 10 → F) (kappa : F) :
    rawOrdinaryOriginal z kappa =
      fun i => kappa * (fun j => sourcePointBasis (SourceStatementPoints.points z 0) j.val) i +
        kappa^2 * (fun j => sourcePointBasis (SourceStatementPoints.points z 1) j.val) i +
        kappa^3 * (fun j => sourcePointBasis (SourceStatementPoints.points z 2) j.val) i +
        indicator inactive i := by
  funext i
  simp only [rawOrdinaryOriginal, sourceOriginalWeight_eq, Bool.false_eq_true, if_false]
  unfold indicator
  ring

theorem transported_original_decomposition (z : Fin 10 → F) (kappa : F) :
    transportDual inactive 1023 order (rawOrdinaryOriginal z kappa) =
      fun i =>
        kappa * transportDual inactive 1023 order
          (fun j => sourcePointBasis (SourceStatementPoints.points z 0) j.val) i +
        kappa^2 * transportDual inactive 1023 order
          (fun j => sourcePointBasis (SourceStatementPoints.points z 1) j.val) i +
        kappa^3 * transportDual inactive 1023 order
          (fun j => sourcePointBasis (SourceStatementPoints.points z 2) j.val) i +
        pivotMarker (K := F) 1023 order i := by
  change dualLinear inactive 1023 order (rawOrdinaryOriginal z kappa) = _
  rw [original_false_decomposition]
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul,
    inactive_to_pivot inactive 1023 pivot_mem_inactive order]
  rfl

theorem extended_original_decomposition (z : Fin 10 → F) (kappa : F) (r : Nat) :
    extendFin1024 (transportDual inactive 1023 order (rawOrdinaryOriginal z kappa)) r =
      kappa * wp z 0 r + kappa^2 * wp z 1 r + kappa^3 * wp z 2 r + marker r := by
  rw [transported_original_decomposition]
  rw [extend_linear kappa (kappa^2) _ _, extend_linear 1 (kappa^3) _ _]
  simp only [one_mul, wp, marker]
  ring

theorem transpose_original_decomposition (half a b c kappa : F) (z : Fin 10 → F) (r : Nat) :
    sourceChordTranspose half
      (extendFin1024 (transportDual inactive 1023 order (rawOrdinaryOriginal z kappa))) a b c r =
      kappa * pointWeight half a b c (SourceStatementPoints.points z 0) r +
        kappa^2 * pointWeight half a b c (SourceStatementPoints.points z 1) r +
        kappa^3 * pointWeight half a b c (SourceStatementPoints.points z 2) r +
        sourceChordTranspose half marker a b c r := by
  have hext : extendFin1024 (transportDual inactive 1023 order (rawOrdinaryOriginal z kappa)) =
      fun r => kappa * wp z 0 r +
        (kappa^2 * wp z 1 r + (kappa^3 * wp z 2 r + marker r)) := by
    funext r
    rw [extended_original_decomposition]
    ring
  rw [hext]
  rw [source_chord_transpose_linear half kappa 1 a b c (wp z 0)
    (fun r => kappa * wp z 1 r + (kappa^2 * wp z 2 r + marker r)) r]
  simp only [one_mul]
  rw [source_chord_transpose_linear half (kappa^2) 1 a b c (wp z 1)
    (fun r => kappa * wp z 2 r + marker r) r]
  simp only [one_mul]
  rw [source_chord_transpose_linear half (kappa^3) 1 a b c (wp z 2) marker r]
  simp only [one_mul, wp]
  ring

theorem raw_ordinary_weight_decomposition
    (half a b c kappa tau : F) (z : Fin 10 → F) (r : Nat) :
    rawOrdinaryWeight half a b c kappa tau z r =
      kappa * pointWeight half a b c (SourceStatementPoints.points z 0) r +
        kappa^2 * pointWeight half a b c (SourceStatementPoints.points z 1) r +
        kappa^3 * pointWeight half a b c (SourceStatementPoints.points z 2) r +
        sourceChordTranspose half marker a b c r +
        (if r = 1023 then tau else 0) +
        (if r = 1022 then tau^2 * b else 0) -
        (if r = 1021 then tau^2 * c else 0) := by
  unfold rawOrdinaryWeight sourceQuotientWeights
  rw [sourceImageUpdates_apply, transpose_original_decomposition]
  simp only [Bool.false_eq_true, if_false]
  ring

#print axioms pivot_mem_inactive
#print axioms original_false_decomposition
#print axioms transported_original_decomposition
#print axioms extended_original_decomposition
#print axioms transpose_original_decomposition
#print axioms raw_ordinary_weight_decomposition

end
end AspisV8R19.R788OrdinaryPointDecomposition

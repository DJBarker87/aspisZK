import AspisV8R19.R785SourceTransposeLinear
import AspisV8R19.R740SparsePointObservation

/-! Function-level decomposition of the selected ordinary source weights. -/
set_option autoImplicit false
namespace AspisV8R19.R788OrdinaryPointDecomposition
set_option maxRecDepth 4096

open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R785SourceTransposeLinear
noncomputable section

variable {F : Type*} [CommRing F]

def wp (z : Fin 10 → F) (p : Fin 3) : Nat → F :=
  extendFin1024 (transportDual inactive 1023 order
    (fun j => sourcePointBasis (SourceStatementPoints.points z p) j.val))

def marker : Nat → F :=
  extendFin1024 (fun j : Fin 1024 => if order j = 1023 then 1 else 0)

theorem pivot_mem_inactive : (1023 : Fin 1024) ∈ inactive := by decide

theorem extend_linear (x y : F) (u v : Fin 1024 → F) (r : Nat) :
    extendFin1024 (fun i => x * u i + y * v i) r =
      x * extendFin1024 u r + y * extendFin1024 v r := by
  unfold extendFin1024
  split <;> simp <;> ring

private theorem transport_original_decomposition_at
    (z : Fin 10 → F) (kappa : F) (j : Fin 1024) :
    transportDual inactive 1023 order (rawOrdinaryOriginal z kappa) j =
      kappa * transportDual inactive 1023 order
        (fun i => sourcePointBasis (SourceStatementPoints.points z 0) i.val) j +
      kappa^2 * transportDual inactive 1023 order
        (fun i => sourcePointBasis (SourceStatementPoints.points z 1) i.val) j +
      kappa^3 * transportDual inactive 1023 order
        (fun i => sourcePointBasis (SourceStatementPoints.points z 2) i.val) j +
      (if order j = 1023 then 1 else 0) := by
  by_cases hp : order j = 1023
  · simp [transportDual, rawOrdinaryOriginal, sourceOriginalWeight_eq,
      hp, pivot_mem_inactive]
    ring
  · by_cases hi : order j ∈ inactive.erase (1023 : Fin 1024)
    · have hinactive : order j ∈ inactive := (Finset.mem_erase.mp hi).2
      simp [transportDual, rawOrdinaryOriginal, sourceOriginalWeight_eq,
        hp, hi, hinactive, pivot_mem_inactive]
      ring
    · have hnotinactive : order j ∉ inactive := by
        intro h
        exact hi (Finset.mem_erase.mpr ⟨hp, h⟩)
      simp [transportDual, rawOrdinaryOriginal, sourceOriginalWeight_eq,
        hp, hi, hnotinactive]


theorem transported_original_decomposition (z : Fin 10 → F) (kappa : F) :
    transportDual inactive 1023 order (rawOrdinaryOriginal z kappa) =
      fun i =>
        kappa * transportDual inactive 1023 order
          (fun j => sourcePointBasis (SourceStatementPoints.points z 0) j.val) i +
        kappa^2 * transportDual inactive 1023 order
          (fun j => sourcePointBasis (SourceStatementPoints.points z 1) j.val) i +
        kappa^3 * transportDual inactive 1023 order
          (fun j => sourcePointBasis (SourceStatementPoints.points z 2) j.val) i +
        (if order i = 1023 then 1 else 0) := by
  funext i
  exact transport_original_decomposition_at z kappa i

theorem extended_original_decomposition (z : Fin 10 → F) (kappa : F) (r : Nat) :
    extendFin1024 (transportDual inactive 1023 order (rawOrdinaryOriginal z kappa)) r =
      kappa * wp z 0 r + kappa^2 * wp z 1 r + kappa^3 * wp z 2 r + marker r := by
  rw [transported_original_decomposition]
  by_cases h : r < 1024
  · simp [extendFin1024, wp, marker, h]
    ring
  · simp [extendFin1024, wp, marker, h]

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
  have h0 := source_chord_transpose_linear half kappa 1 a b c (wp z 0)
    (fun r => kappa^2 * wp z 1 r + (kappa^3 * wp z 2 r + marker r)) r
  rw [show sourceChordTranspose half
      (fun r => kappa * wp z 0 r + (kappa^2 * wp z 1 r +
        (kappa^3 * wp z 2 r + marker r))) a b c r = _ by simpa only [one_mul] using h0]
  have h1 := source_chord_transpose_linear half (kappa^2) 1 a b c (wp z 1)
    (fun r => kappa^3 * wp z 2 r + marker r) r
  rw [show sourceChordTranspose half
      (fun r => kappa^2 * wp z 1 r + (kappa^3 * wp z 2 r + marker r)) a b c r = _ by
        simpa only [one_mul] using h1]
  have h2 := source_chord_transpose_linear half (kappa^3) 1 a b c (wp z 2) marker r
  rw [show sourceChordTranspose half
      (fun r => kappa^3 * wp z 2 r + marker r) a b c r = _ by
        simpa only [one_mul] using h2]
  simp only [one_mul, wp, pointWeight]
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

#print axioms pivot_mem_inactive
#print axioms transported_original_decomposition
#print axioms extended_original_decomposition
#print axioms transpose_original_decomposition
#print axioms raw_ordinary_weight_decomposition

end
end AspisV8R19.R788OrdinaryPointDecomposition

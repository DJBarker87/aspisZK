import AspisV8R19.R789MappedJointNormalization
import AspisV8R15.ExactTowerBase
namespace AspisV8R19.R791QM31JointNormalization
open AspisV8R15.ExactTowerBase
open AspisV8R19.R779FixedPoint1LowKernel
open AspisV8R19.R748JointWitnessPointEntry (z)
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R746SelectedJointMinor
noncomputable section
set_option autoImplicit false

def witnessEmbedding : M →+* QM31Exact :=
  (algebraMap CM31Exact QM31Exact).comp (algebraMap M31Exact CM31Exact)

local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hh := congrArg (fun x : QM31Exact => x.re.re) h
  change (2 : M31Exact) = 0 at hh
  exact (by decide : (2 : M31Exact) ≠ 0) hh⟩

theorem qm31_normalized_matrix (t : Fin 22 → QM31Exact)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    normalizedSelectedMatrix (witnessEmbedding half)
      (witnessEmbedding (536870912 : M)) 7 2 3 5 0
      (fun i => witnessEmbedding (z i)) t ht noneOne =
    chosenSourceMatrix (witnessEmbedding half)
      (witnessEmbedding (536870912 : M)) 7 2 3 5 0
      (fun i => witnessEmbedding (z i)) :=
  R789MappedJointNormalization.mapped_normalized_matrix witnessEmbedding t ht noneOne

#print axioms witnessEmbedding
#print axioms qm31_normalized_matrix
end
end AspisV8R19.R791QM31JointNormalization
rcePointBasis (SourceStatementPoints.points z 0) i.val) j +
      kappa^2 * transportDual inactive 1023 order
        (fun i => sourcePointBasis (SourceStatementPoints.points z 1) i.val) j +
      kappa^3 * transportDual inactive 1023 order
        (fun i => sourcePointBasis (SourceStatementPoints.points z 2) i.val) j +
      (if order j = 1023 then 1 else 0) := by
  by_cases hp : order j = 1023
  · subst hp
    simp [transportDual, rawOrdinaryOriginal, sourceOriginalWeight_eq,
      pivot_mem_inactive]
    ring
  · by_cases hi : order j ∈ inactive.erase (1023 : Fin 1024)
    · have hinactive : order j ∈ inactive := (Finset.mem_erase.mp hi).2
      simp [transportDual, rawOrdinaryOriginal, sourceOriginalWeight_eq,
        hp, hi, hinactive]
      ring
    · have hnotinactive : order j ∉ inactive := by
        intro h
        exact hi (Finset.mem_erase.mpr ⟨hp, h⟩)
      simp [transportDual, rawOrdinaryOriginal, sourceOriginalWeight_eq,
        hp, hi, hnotinactive]
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
        (if order i = 1023 then 1 else 0) := by
  funext i
  exact transport_original_decomposition_at z kappa i

theorem extended_original_decomposition (z : Fin 10 → F) (kappa : F) (r : Nat) :
    extendFin1024 (transportDual inactive 1023 order (rawOrdinaryOriginal z kappa)) r =
      kappa * wp z 0 r + kappa^2 * wp z 1 r + kappa^3 * wp z 2 r + marker r := by
  rw [transported_original_decomposition]
  unfold extendFin1024 wp marker
  split <;> simp <;> ring

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
    (fun r => kappa^2 * wp z 1 r + (kappa^3 * wp z 2 r + marker r)) r]
  simp only [one_mul]
  rw [source_chord_transpose_linear half (kappa^2) 1 a b c (wp z 1)
    (fun r => kappa^3 * wp z 2 r + marker r) r]
  simp only [one_mul]
  rw [source_chord_transpose_linear half (kappa^3) 1 a b c (wp z 2) marker r]
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
  ring

#print axioms pivot_mem_inactive
#print axioms transported_original_decomposition
#print axioms extended_original_decomposition
#print axioms transpose_original_decomposition
#print axioms raw_ordinary_weight_decomposition

end
end AspisV8R19.R788OrdinaryPointDecomposition

import AspisV8R19.R791QM31JointNormalization
import AspisV8R19.R792JointSourceMatrixHom
namespace AspisV8R19.R794QM31JointDeterminantTransfer
open AspisV8R15.ExactTowerBase
open AspisV8R19.R779FixedPoint1LowKernel
open AspisV8R19.R748JointWitnessPointEntry (z)
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R791QM31JointNormalization
noncomputable section
set_option autoImplicit false
local instance : Fact (Nat.Prime 2147483647) := m31PrimeFact
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hh := congrArg (fun x : QM31Exact => x.re.re) h
  change (2 : M31Exact) = 0 at hh
  exact (by decide : (2 : M31Exact) ≠ 0) hh⟩

 theorem raw_witness_matrix_map :
    witnessEmbedding.mapMatrix (chosenSourceMatrix half (536870912 : M) 7 2 3 5 0 z) =
      chosenSourceMatrix (witnessEmbedding half) (witnessEmbedding (536870912 : M))
        7 2 3 5 0 (fun i => witnessEmbedding (z i)) := by
  simpa only [map_ofNat,map_zero] using
    R792JointSourceMatrixHom.map_chosen_matrix witnessEmbedding half (536870912 : M)
      7 2 3 5 0 z

 theorem normalized_qm31_det_eq (t : Fin 22 → QM31Exact)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    (normalizedSelectedMatrix (witnessEmbedding half)
      (witnessEmbedding (536870912 : M)) 7 2 3 5 0
      (fun i => witnessEmbedding (z i)) t ht noneOne).det =
      witnessEmbedding (chosenSourceMatrix half (536870912 : M) 7 2 3 5 0 z).det := by
  rw [qm31_normalized_matrix, witnessEmbedding.map_det, raw_witness_matrix_map]

 theorem normalized_qm31_det_ne_zero_of_source
    (hsource : (chosenSourceMatrix half (536870912 : M) 7 2 3 5 0 z).det ≠ 0)
    (t : Fin 22 → QM31Exact) (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    (normalizedSelectedMatrix (witnessEmbedding half)
      (witnessEmbedding (536870912 : M)) 7 2 3 5 0
      (fun i => witnessEmbedding (z i)) t ht noneOne).det ≠ 0 := by
  rw [normalized_qm31_det_eq]
  intro h
  apply hsource
  apply witnessEmbedding.injective
  simpa only [map_zero] using h

#print axioms raw_witness_matrix_map
#print axioms normalized_qm31_det_eq
#print axioms normalized_qm31_det_ne_zero_of_source
end
end AspisV8R19.R794QM31JointDeterminantTransfer

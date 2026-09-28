import V7CallerCurrentReleaseR26K1QueryWeightBridge
import V7CallerCurrentReleaseR26QueryClaimSemantics

/-!
# Current R26 authenticated query claim in the maintained K1 field

The production insertion computes the dot product of the sixteen authenticated
values with shifted powers `rho^1, ..., rho^16`.  This file transports that
source theorem through the explicit R26-to-K1 ring homomorphism and identifies
the result with K1's `shiftedQueryBatchClaim`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26K1QueryClaimBridge

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26QueryClaimSemantics
open AspisK1.V7Tag73BatchedQuerySourceBridge

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator
abbrev SourceQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

/-- Transporting the literal sixteen-term source dot product produces exactly
the shifted query claim used by K1. -/
theorem shiftedSourceQueryClaim_eq_model
    (rho : SourceQM31) (values : Nat → SourceQM31) :
    sourceQm31ToModel
        (∑ ordinal ∈ Finset.range 16,
          rho ^ (ordinal + 1) * values ordinal) =
      shiftedQueryBatchClaim
        (fun ordinal : Fin 16 => sourceQm31ToModel (values ordinal.val))
        (sourceQm31ToModel rho) := by
  classical
  rw [shiftedQueryBatchClaim_eq_sum]
  change sourceQm31ToModelHom
      (∑ ordinal ∈ Finset.range 16,
        rho ^ (ordinal + 1) * values ordinal) = _
  rw [map_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro ordinal _
  rw [map_mul, map_pow]
  rfl

/-- The claim increment returned by an accepted production insertion is the
maintained K1 shifted claim of the authenticated values. -/
theorem accepted_insertion_claim_increment_model_exact
    (weights : RawWeights) (runningClaim : RawQM31)
    (queries : Array Std.U32 16#usize)
    (authenticated : v6_query_batch.V6AuthenticatedQueryBatch)
    (rho claimIncrement : RawQM31)
    (weightsAfter : RawWeights) (runningClaimAfter : RawQM31)
    (rhoExact : SourceQM31)
    (rhoCanonical : GeneratedCanonicalQM31 rho)
    (rhoExactEq : generatedQm31ToExact rho = rhoExact)
    (valuesCanonical : ∀ ordinal, ordinal < 16 →
      GeneratedCanonicalQM31 authenticated.values.val[ordinal]!)
    (trace :
      V7CallerCurrentReleaseR26QueryBatchInsertion.AcceptedQueryBatchInsertionTrace
        weights runningClaim queries authenticated rho claimIncrement
        weightsAfter runningClaimAfter) :
    GeneratedCanonicalQM31 claimIncrement ∧
      sourceQm31ToModel (generatedQm31ToExact claimIncrement) =
        shiftedQueryBatchClaim
          (fun ordinal : Fin 16 => sourceQm31ToModel
            (generatedQm31ToExact authenticated.values.val[ordinal.val]!))
          (sourceQm31ToModel rhoExact) := by
  obtain ⟨incrementCanonical, incrementExact⟩ :=
    accepted_insertion_claim_increment_exact weights runningClaim queries
      authenticated rho claimIncrement weightsAfter runningClaimAfter rhoExact
      rhoCanonical rhoExactEq valuesCanonical trace
  refine ⟨incrementCanonical, ?_⟩
  rw [incrementExact]
  exact shiftedSourceQueryClaim_eq_model rhoExact
    (fun ordinal => generatedQm31ToExact authenticated.values.val[ordinal]!)

#print axioms shiftedSourceQueryClaim_eq_model
#print axioms accepted_insertion_claim_increment_model_exact

end V7CallerCurrentReleaseR26K1QueryClaimBridge

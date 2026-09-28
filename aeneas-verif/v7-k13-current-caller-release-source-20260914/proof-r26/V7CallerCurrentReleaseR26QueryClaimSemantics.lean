import V7CallerCurrentReleaseR26Qm31DotShortOuterLoop
import V7CallerCurrentReleaseR26QueryBatchAppend
import V7CallerCurrentReleaseR26QueryScaleExactLoop

/-!
# Exact current R26 authenticated query claim

This file joins the verified shifted scale loop to the verified production
`qm31_dot` short path.  It identifies the source-returned claim increment with
the exact shifted-power dot product over the sixteen authenticated folded
values, then transports that fact through the source running-claim addition.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26QueryClaimSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotShortOuterLoop
open V7CallerCurrentReleaseR26QueryBatchAppend
open V7CallerCurrentReleaseR26QueryScaleExactStep
open V7CallerCurrentReleaseR26QueryScaleExactLoop

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited field.QM31 := ⟨field.QM31.ZERO⟩

/-- The literal claim returned by an accepted query insertion is the exact
shifted-power dot product over the authenticated folded values. -/
theorem accepted_insertion_claim_increment_exact
    (weights : RawWeights) (runningClaim : RawQM31)
    (queries : Array Std.U32 16#usize)
    (authenticated : v6_query_batch.V6AuthenticatedQueryBatch)
    (rho claimIncrement : RawQM31)
    (weightsAfter : RawWeights) (runningClaimAfter : RawQM31)
    (rhoExact : ExactQM31)
    (rhoCanonical : GeneratedCanonicalQM31 rho)
    (rhoExactEq : generatedQm31ToExact rho = rhoExact)
    (valuesCanonical : ∀ ordinal, ordinal < 16 →
      GeneratedCanonicalQM31 authenticated.values.val[ordinal]!)
    (trace :
      V7CallerCurrentReleaseR26QueryBatchInsertion.AcceptedQueryBatchInsertionTrace
        weights runningClaim queries authenticated rho claimIncrement
        weightsAfter runningClaimAfter) :
    GeneratedCanonicalQM31 claimIncrement ∧
      generatedQm31ToExact claimIncrement =
        ∑ ordinal ∈ Finset.range 16,
          rhoExact ^ (ordinal + 1) *
            generatedQm31ToExact authenticated.values.val[ordinal]! := by
  have scalePrefix : ShiftedScalePrefix rhoExact trace.scales 16#usize :=
    successful_scale_loop_has_exact_shifted_powers rho rhoExact
      trace.preparedRho trace.seed trace.scales rhoCanonical rhoExactEq
      trace.seedSuccess trace.preparedRhoSuccess trace.scalesLoopSuccess
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_dot_sixteen_corresponds
      (Array.to_slice trace.scales) (Array.to_slice authenticated.values)
      (by simp [Array.to_slice]) (by simp [Array.to_slice])
      (by
        intro ordinal ordinalBound
        exact scalePrefix.1 ordinal
          (by simpa [Array.to_slice] using ordinalBound))
      (by
        intro ordinal ordinalBound
        exact valuesCanonical ordinal
          (by simpa [Array.to_slice] using ordinalBound))
  have outputExact : out = claimIncrement :=
    Result.ok.inj (outRun.symm.trans trace.claimDotSuccess)
  subst out
  refine ⟨outCanonical, outExact.trans ?_⟩
  apply Finset.sum_congr rfl
  intro ordinal ordinalMem
  have ordinalBound : ordinal < 16 := by simpa using ordinalMem
  have scaleExact :
      generatedQm31ToExact trace.scales.val[ordinal]! =
        rhoExact ^ (ordinal + 1) := by
    simpa [exactScaleAt] using
      scalePrefix.2.2.2 ordinal ordinalBound
  simpa [Array.to_slice] using congrArg
    (fun value => value *
      generatedQm31ToExact authenticated.values.val[ordinal]!) scaleExact

/-- The running claim after the accepted insertion is the incoming exact claim
plus the authenticated shifted-power dot product. -/
theorem accepted_insertion_running_claim_with_query_exact
    (weights : RawWeights) (runningClaim : RawQM31)
    (queries : Array Std.U32 16#usize)
    (authenticated : v6_query_batch.V6AuthenticatedQueryBatch)
    (rho claimIncrement : RawQM31)
    (weightsAfter : RawWeights) (runningClaimAfter : RawQM31)
    (rhoExact : ExactQM31)
    (runningCanonical : GeneratedCanonicalQM31 runningClaim)
    (rhoCanonical : GeneratedCanonicalQM31 rho)
    (rhoExactEq : generatedQm31ToExact rho = rhoExact)
    (valuesCanonical : ∀ ordinal, ordinal < 16 →
      GeneratedCanonicalQM31 authenticated.values.val[ordinal]!)
    (trace :
      V7CallerCurrentReleaseR26QueryBatchInsertion.AcceptedQueryBatchInsertionTrace
        weights runningClaim queries authenticated rho claimIncrement
        weightsAfter runningClaimAfter) :
    GeneratedCanonicalQM31 runningClaimAfter ∧
      generatedQm31ToExact runningClaimAfter =
        generatedQm31ToExact runningClaim +
          ∑ ordinal ∈ Finset.range 16,
            rhoExact ^ (ordinal + 1) *
              generatedQm31ToExact authenticated.values.val[ordinal]! := by
  obtain ⟨incrementCanonical, incrementExact⟩ :=
    accepted_insertion_claim_increment_exact weights runningClaim queries
      authenticated rho claimIncrement weightsAfter runningClaimAfter rhoExact
      rhoCanonical rhoExactEq valuesCanonical trace
  obtain ⟨afterCanonical, afterExact⟩ :=
    accepted_insertion_running_claim_exact weights runningClaim queries
      authenticated rho claimIncrement weightsAfter runningClaimAfter
      runningCanonical incrementCanonical trace
  exact ⟨afterCanonical, afterExact.trans (by rw [incrementExact])⟩

#print axioms accepted_insertion_claim_increment_exact
#print axioms accepted_insertion_running_claim_with_query_exact

end V7CallerCurrentReleaseR26QueryClaimSemantics

import S4Tx1CallerLoopRootV1
import CallerStage2SourceConstructor
import S4TenNamedCallRootV1
import S4Tx1TenFieldConsumerV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4Tx1CurrentCallerTenFieldConsumerV1
open AspisR1Stage2
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4CallerStage2SourceConstructorV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4TwelveQueryFieldResultsRootV1
open AspisR1S4Tx1TenFieldResultsRootV1 (CPrepared CWide)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

-- Keep the generated query implementation opaque while matching the mapped caller carriers.
attribute [local irreducible] AspisR1Stage2.verifier.candidate.query_loop AspisR1Stage2.verifier.candidate.queryWithOps

/-- Starting from actual CurrentCaller carrier values, map the source-prepared
state into the stage-2 query loop and project its ten accepted calls to field
result witnesses. Caller preparation, scan, powers, and loop success are kept
as hypotheses so this consumer isolates only the carrier-conversion boundary. -/
theorem current_caller_loop_has_ten_field_results
    (aops : AccumulateOps)
    (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops)
    (rest : QueryOps)
    (proof : Slice U8)
    (p : CPrepared)
    (g : Array CWide 29#usize)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (geometry : AspisR1CurrentCaller.verifier.QueryGeometry)
    (start : AspisR1CurrentCaller.verifier.Accumulator)
    (finish : verifier.Accumulator)
    (b : AspisR1CurrentCaller.verifier.BatchedWeights)
    (bout : verifier.BatchedWeights)
    (gamma : ClaimE)
    (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hmap : fullArrayToCurrent (arrayWideToStage g) = claimArrayToFast claimPowers)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hstart : start.next = 0#usize)
    (hloop : verifier.candidate.query_loop
      (AspisR1S4Tx1TenFieldResultsRootV1.fieldCall aops rest headOps)
      proof (preparedToStage p) (accumulatorToStage start) (arrayWideToStage g)
      (obs.map (fun f => fun phase => f (phaseToCaller phase)))
      (geometryToStage geometry) (batchedWeightsToStage b) 10#usize =
      .ok (.Ok (finish,bout))) :
    ∀ k : Fin 10, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
      a0.next.val = k.val ∧
      verifier.candidate.queryWithOps aops
        (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
        proof (preparedToStage p) a0 (arrayWideToStage g)
        (obs.map (fun f => fun phase => f (phaseToCaller phase)))
        (geometryToStage geometry) b0 = .ok (.Ok (a1,b1)) ∧
      QueryFieldEvidence headOps proof (preparedToStage p) (arrayWideToStage g) a0 := by
  have hstartStage : (accumulatorToStage start).next.val = 0 := by
    change start.next.val = 0
    simpa [hstart]
  have hloopNamed : verifier.candidate.query_loop
      (AspisR1S4TenNamedCallRootV1.namedCall aops headOps rest)
      proof (preparedToStage p) (accumulatorToStage start) (arrayWideToStage g)
      (obs.map (fun f => fun phase => f (phaseToCaller phase)))
      (geometryToStage geometry) (batchedWeightsToStage b) 10#usize =
      .ok (.Ok (finish,bout)) := by
    change verifier.candidate.query_loop
      (AspisR1S4TenNamedCallRootV1.namedCall aops headOps rest)
      proof (preparedToStage p) (accumulatorToStage start) (arrayWideToStage g)
      (obs.map (fun f => fun phase => f (phaseToCaller phase)))
      (geometryToStage geometry) (batchedWeightsToStage b) 10#usize =
      .ok (.Ok (finish,bout))
    exact hloop
  exact AspisR1S4Tx1TenFieldConsumerV1.mapped_caller_loop_has_ten_field_results
    aops headOps rest proof (preparedToStage p) (arrayWideToStage g)
    (obs.map (fun f => fun phase => f (phaseToCaller phase)))
    (geometryToStage geometry) (accumulatorToStage start) finish
    (batchedWeightsToStage b) bout gamma claimPowers hgamma hpowers hmap hscan
    hstartStage hloopNamed

#print axioms current_caller_loop_has_ten_field_results
end AspisR1S4Tx1CurrentCallerTenFieldConsumerV1

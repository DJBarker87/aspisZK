import S4Tx1CallerLoopConcreteV4
import AspisR1AccumulatorNewConcreteChildrenV4
import S4Tx1SplitGuardRootV1
import S4TenNamedCallRootV1
import S4ConcreteKernelOpsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4Tx1TenFieldResultsRootV1
open AspisR1Stage2
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4AccumulatorNewConcreteChildrenV4
open AspisR1S4Tx1SplitGuardRootV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4TwelveQueryFieldResultsRootV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

theorem source_caller_reaches_prepared_loop
    (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops) {H : Type}
    (ops : COps H) (aops : AccumulateOps) (rest : QueryOps)
    (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (bytes : alloc.vec.Vec U8)
    (filled : Usize → CQm → Result (core.result.Result (alloc.vec.Vec CQm) CCoreError))
    (hscanBinding : ops.canonicalScan proof = .ok (.Ok ()) →
      MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hprepareBinding : ∀ (zero : CWide) (p : CPrepared) (g : Array CWide 29#usize),
      ops.prepare inst public1 proof hash obs (Array.repeat 29#usize zero) = .ok (.Ok p,g) →
      ∃ (gamma : ClaimE) (powers : Array ClaimE 29#usize),
        ClaimCanonical gamma ∧
        AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers ∧
        fullArrayToCurrent (arrayWideToStage g) = claimArrayToFast powers)
    (h : AspisR1CallerV4Tx1OpsCut.tx1
      (sourceCaller ops aops rest headOps filled)
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    k = 10#usize ∧ ∃ (p : CPrepared) (g : Array CWide 29#usize)
      (a : AspisR1CurrentCaller.verifier.Accumulator)
      (geometry : AspisR1CurrentCaller.verifier.QueryGeometry)
      (b : AspisR1CurrentCaller.verifier.BatchedWeights)
      (outS : verifier.Accumulator) (boutS : verifier.BatchedWeights)
      (gamma : ClaimE) (powers : Array ClaimE 29#usize),
      (∃ zero : CWide, ops.prepare inst public1 proof hash obs
        (Array.repeat 29#usize zero) = .ok (.Ok p,g)) ∧
      ClaimCanonical gamma ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers ∧
      fullArrayToCurrent (arrayWideToStage g) = claimArrayToFast powers ∧
      MultiproofParserRef.parser_reference.scan proof = .ok true ∧
      a.next = 0#usize ∧
      verifier.candidate.query_loop (fieldCall aops rest headOps) proof (preparedToStage p)
        (accumulatorToStage a) (arrayWideToStage g)
        (obs.map (fun f => fun phase => f (phaseToCaller phase)))
        (geometryToStage geometry) (batchedWeightsToStage b) 10#usize = .ok (.Ok (outS,boutS)) := by
  obtain ⟨hk,p,g,a,geometry,b,outS,boutS,hscan,⟨zero,hprep⟩,hstart,hloop⟩ :=
    source_caller_reaches_ten_loop headOps ops aops rest inst public1 public_bytes proof k hash obs
      bytes filled h
  obtain ⟨gamma,powers,hgamma,hpowers,hg⟩ := hprepareBinding zero p g hprep
  exact ⟨hk,p,g,a,geometry,b,outS,boutS,gamma,powers,⟨zero,hprep⟩,
    hgamma,hpowers,hg,hscanBinding hscan,hstart,hloop⟩

#print axioms source_caller_reaches_prepared_loop
end AspisR1S4Tx1TenFieldResultsRootV1

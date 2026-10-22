import S4Tx1TypedOpeningsV1
import S4QueryReturnedSemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4Tx1ReturnedSemanticsV1
open AspisR1S4CandidateCallerPreparedRootV1
open AspisR1Stage2
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4Tx1SplitGuardRootV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4TwelveQueryFieldResultsRootV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

attribute [local irreducible] verifier.candidate.query_loop verifier.candidate.queryWithOps

theorem candidate_source_tx1_success_ten_returned_local_batches
    {H : Type}
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
      (sourceCaller ops aops rest filled)
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    k = 10#usize ∧ ∃ (p : CPrepared) (g : Array CWide 29#usize)
      (geometry : AspisR1CurrentCaller.verifier.QueryGeometry)
      (gamma : ClaimE) (powers : Array ClaimE 29#usize),
      ClaimCanonical gamma ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers ∧
      fullArrayToCurrent (arrayWideToStage g) = claimArrayToFast powers ∧
      ∀ i : Fin 10, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val = i.val ∧
        candidateCall aops rest proof (preparedToStage p) a0 (arrayWideToStage g)
          (obs.map (fun f => fun phase => f (phaseToCaller phase)))
          (geometryToStage geometry) b0 = .ok (.Ok (a1,b1)) ∧
        AspisR1S4QueryReturnedSemanticsV1.CandidateQueryReturnedLocalBatchEvidence
          rest proof (preparedToStage p) a0 (arrayWideToStage g) powers gamma := by
  obtain ⟨hk,p,g,geometry,gamma,powers,hgamma,hpowers,hg,all⟩ :=
    AspisR1.S4Tx1TypedOpeningsV1.candidate_source_tx1_success_ten_typed_openings
      ops aops rest inst public1 public_bytes proof k hash obs bytes filled
      hscanBinding hprepareBinding h
  refine ⟨hk,p,g,geometry,gamma,powers,hgamma,hpowers,hg,?_⟩
  intro i
  obtain ⟨a0,a1,b0,b1,hindex,hcall,htyped⟩ := all i
  refine ⟨a0,a1,b0,b1,hindex,hcall,?_⟩
  exact AspisR1S4QueryReturnedSemanticsV1.typed_opening_returned_local_batches
    rest proof (preparedToStage p) a0 (arrayWideToStage g) powers gamma
    hgamma hpowers htyped
#print axioms candidate_source_tx1_success_ten_returned_local_batches
end AspisR1.S4Tx1ReturnedSemanticsV1

import S4CandidateCallerPreparedRootV1
import S4CandidateLoopActualCallsV1
import S4V10CandidateQueryFieldEvidenceV1
import S4Tx1SplitGuardRootV1
import S4TenNamedCallRootV1
import S4ConcreteKernelOpsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4CandidateTx1OutputFieldsRootV1
open AspisR1S4CandidateCallerPreparedRootV1
open AspisR1Stage2
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4Tx1SplitGuardRootV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4TwelveQueryFieldResultsRootV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

attribute [local irreducible] verifier.candidate.query_loop verifier.candidate.queryWithOps

theorem candidate_source_tx1_success_ten_output_field_results
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
        AspisR1FastDotsV10CandidateQueryFieldEvidenceV1.CandidateQueryFieldEvidence
          rest proof (preparedToStage p) a0 (arrayWideToStage g) powers := by
  obtain ⟨hk,p,g,a,geometry,b,outS,boutS,gamma,powers,hprep,hgamma,hpowers,hg,hscan,hstart,hloop⟩ :=
    source_caller_reaches_prepared_loop ops aops rest inst public1 public_bytes proof k hash obs
      bytes filled hscanBinding hprepareBinding h
  have hs : (accumulatorToStage a).next.val = 0 := by
    change a.next.val = 0
    rw [hstart]
    rfl
  have hf : candidateCall aops rest = (fun proof p a g obs geometry b =>
      verifier.candidate.queryWithOps aops
        (AspisR1FastDotsV10ConcreteQueryOpsBuilderV1.concreteCandidateQueryOps rest)
        proof p a g obs geometry b) := rfl
  have hloopCandidate := Eq.mp (congrArg (fun call : QueryCall =>
    verifier.candidate.query_loop call proof (preparedToStage p) (accumulatorToStage a)
      (arrayWideToStage g) (obs.map (fun f => fun phase => f (phaseToCaller phase)))
      (geometryToStage geometry) (batchedWeightsToStage b) 10#usize = .ok (.Ok (outS,boutS))) hf) hloop
  have all := AspisR1S4CandidateLoopActualCallsV1.candidate_ten_queries_have_actual_call_field_results
    aops rest proof (preparedToStage p) (arrayWideToStage g)
    (obs.map (fun f => fun phase => f (phaseToCaller phase)))
    (geometryToStage geometry) (accumulatorToStage a) outS (batchedWeightsToStage b) boutS
    gamma powers hgamma hpowers hg hscan hs hloopCandidate
  refine ⟨hk,p,g,geometry,gamma,powers,hgamma,hpowers,hg,?_⟩
  intro i
  obtain ⟨a0,a1,b0,b1,hindex,hcall,_⟩ := all i
  refine ⟨a0,a1,b0,b1,hindex,hcall,?_⟩
  exact AspisR1FastDotsV10CandidateQueryFieldEvidenceV1.candidate_query_success_field_evidence
    aops rest proof (preparedToStage p) a0 (arrayWideToStage g)
    (obs.map (fun f => fun phase => f (phaseToCaller phase)))
    (geometryToStage geometry) b0 (.Ok (a1,b1)) gamma powers
    hgamma hpowers hg hscan hcall

#print axioms candidate_source_tx1_success_ten_output_field_results
end AspisR1S4CandidateTx1OutputFieldsRootV1

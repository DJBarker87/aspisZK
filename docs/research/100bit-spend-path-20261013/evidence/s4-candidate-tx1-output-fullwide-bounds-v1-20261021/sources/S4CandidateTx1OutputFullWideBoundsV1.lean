import S4CandidateTx1OutputFieldsRootV1
import S4V10CandidateQueryFullWideBoundsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4CandidateTx1OutputFullWideBoundsV1

open AspisR1Stage2
open AspisR1S4CandidateCallerPreparedRootV1
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)
open AspisR1FastDotsV10CandidateQueryFieldEvidenceV1 (CandidateQueryFieldEvidence)
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1 (concreteCandidateQueryOps)
open AspisR1FastDotsV10CandidateQueryFullWideBoundsV1 (FullCoordinateBound FullWide)

/-- For one successful source `tx1`, each of the ten reached actual candidate
query calls returns the same Stage2 `FullWide` array on which the fieldwise
canonical-coordinate bounds are established.  The query result and bounds
are not supplied as independent success facts: each slot is derived from the
same candidate-query evidence produced by the parent loop theorem. -/
theorem candidate_source_tx1_success_ten_fullwide_coordinate_bounds
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
      ∀ i : Fin 10, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights)
        (q : Slice U8) (values : Array AspisR1FastDotsV10CandidateQueryFullWideBoundsV1.FullWide 4#usize),
        a0.next.val = i.val ∧
        candidateCall aops rest proof (preparedToStage p) a0 (arrayWideToStage g)
          (obs.map (fun f => fun phase => f (phaseToCaller phase)))
          (geometryToStage geometry) b0 = .ok (.Ok (a1,b1)) ∧
        sourceOpening proof a0.next = .ok q ∧
        (concreteCandidateQueryOps rest).dots q (arrayWideToStage g) = .ok values ∧
        (∀ x ∈ values.val, FullCoordinateBound x) := by
  obtain ⟨hk,p,g,geometry,gamma,powers,hgamma,hpowers,hg,hslots⟩ :=
    AspisR1S4CandidateTx1OutputFieldsRootV1.candidate_source_tx1_success_ten_output_field_results
      ops aops rest inst public1 public_bytes proof k hash obs bytes filled
      hscanBinding hprepareBinding h
  refine ⟨hk,p,g,geometry,gamma,powers,hgamma,hpowers,hg,?_⟩
  intro i
  obtain ⟨a0,a1,b0,b1,hindex,hcall,hevidence⟩ := hslots i
  obtain ⟨_,_,q,values,hopening,hdots,hbounds⟩ :=
    AspisR1FastDotsV10CandidateQueryFullWideBoundsV1.candidate_query_fullwide_coordinate_bounds
      rest proof (preparedToStage p) a0 (arrayWideToStage g) powers hevidence
  refine ⟨a0,a1,b0,b1,q,values,hindex,hcall,?_⟩
  exact ⟨hopening,hdots,hbounds⟩

#print axioms candidate_source_tx1_success_ten_fullwide_coordinate_bounds

end AspisR1S4CandidateTx1OutputFullWideBoundsV1

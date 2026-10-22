import S4CandidateLoopFieldTransportV1
import S4TenQueryFieldResultsRootV1
import S4TwelveQueryFieldResultsRootV1
import S4ConcreteKernelOpsRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4CandidateLoopActualCallsV1
open AspisR1Stage2
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1 (concreteCandidateQueryOps)
open AspisR1S4FullQueryValuesPrefixV1 (full_query_values_success_scanned_field_results)

abbrev FullWide := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev ClaimE := AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE

private theorem adapted_ok_inv
    {A B E : Type} (call : Stage2ContinuationOwnedLoop.Call A B E)
    (a a1 : A) (b b1 : B)
    (h : Stage2ContinuationOwnedLoop.adapt call a b = .ok (.Ok (),a1,b1)) :
    call a b = .ok (.Ok (a1,b1)) := by
  unfold Stage2ContinuationOwnedLoop.adapt at h
  cases hc : call a b with
  | fail e => simp [hc] at h
  | div => simp [hc] at h
  | ok r =>
    cases r with
    | Err e => simp [hc] at h
    | Ok pair =>
      rcases pair with ⟨a2,b2⟩
      have hp : a2=a1 ∧ b2=b1 := by simpa [hc] using h
      rcases hp with ⟨rfl,rfl⟩
      rfl

private theorem candidate_query_step_refines_old
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b b1 : verifier.BatchedWeights) (a1 : verifier.Accumulator)
    (h : verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
      proof p a g obs geometry b = .ok (.Ok (a1,b1))) :
    verifier.candidate.queryWithOps aops
      (AspisR1FastDotsV10QueryOpsResultTransportV1.withOldModelDots concreteOps rest)
      proof p a g obs geometry b = .ok (.Ok (a1,b1)) := by
  exact AspisR1FastDotsV10ConcreteQueryOpsBuilderV1.concrete_candidate_query_refines_old_model
    aops rest proof p a g obs geometry b (.Ok (a1,b1)) h

private theorem candidate_call_field_evidence
    (aops : AccumulateOps) (rest : QueryOps) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
      AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hcandidate : verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
      proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1))) :
    AspisR1S4TwelveQueryFieldResultsRootV1.QueryFieldEvidence concreteOps proof p g a0 := by
  have hold := candidate_query_step_refines_old aops rest proof p a0 g obs geometry b0 b1 a1 hcandidate
  have hold' : verifier.candidate.queryWithOps aops
      (AspisR1S4FullQueryValuesPrefixV1.withS4Callbacks
        (AspisR1FastDotsFourCallbacksForwardRootV1.install concreteOps) rest)
      proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) := by
    simpa [AspisR1FastDotsV10QueryOpsResultTransportV1.withOldModelDots,
      AspisR1FastDotsV10QueryOpsResultTransportV1.oldModelDots,
      AspisR1S4FullQueryValuesPrefixV1.withS4Callbacks] using hold
  exact full_query_values_success_scanned_field_results aops concreteOps rest proof p a0 g
    obs geometry b0 (.Ok (a1,b1)) gamma claimPowers hgamma hpowers hcaller hscan hold'

theorem candidate_ten_queries_have_actual_call_field_results
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
      AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hstart : a.next.val = 0)
    (hloop : verifier.candidate.query_loop
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (concreteCandidateQueryOps rest) proof p a g obs geometry b)
      proof p a g obs geometry b 10#usize = .ok (.Ok (out,bout))) :
    ∀ k : Fin 10, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
      a0.next.val=k.val ∧
      verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
        proof p a0 g obs geometry b0=.ok (.Ok (a1,b1)) ∧
      AspisR1S4TwelveQueryFieldResultsRootV1.QueryFieldEvidence concreteOps proof p g a0 := by
  let call : QueryCall := fun proof p a g obs geometry b =>
    verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest) proof p a g obs geometry b
  have advance : ∀ a a1 b b1, call proof p a g obs geometry b=.ok (.Ok (a1,b1)) →
      a1.next.val=a.next.val+1 := by
    intro a a1 b b1 hc
    exact query_next aops (concreteCandidateQueryOps rest) proof p a a1 g obs geometry b b1 hc
  have chain := AspisR1S4TenQueryFieldResultsRootV1.emitted_ten_ordered_calls
    call proof p g obs geometry advance a out b bout hstart hloop
  intro k
  have hadv : ∀ a a1 b b1,
      Stage2ContinuationOwnedLoop.adapt (fun a b => call proof p a g obs geometry b) a b =
        .ok (.Ok (),a1,b1) → a1.next.val+12=(a.next.val+12)+1 := by
    intro a a1 b b1 hc
    have hs := advance a a1 b b1 (adapted_ok_inv _ a a1 b b1 hc)
    omega
  obtain ⟨a0,a1,b0,b1,hindex,hcall⟩ := AspisR1S4TwelveQueryFieldResultsRootV1.chain_call_at _ _ hadv chain k.val k.isLt
  have hc := adapted_ok_inv _ a0 a1 b0 b1 hcall
  exact ⟨a0,a1,b0,b1,by omega,hc,
    candidate_call_field_evidence aops rest proof p g obs geometry a0 a1 b0 b1
      gamma claimPowers hgamma hpowers hcaller hscan hc⟩

theorem candidate_twelve_queries_have_actual_call_field_results
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
      AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hstart : a.next.val = 10)
    (hloop : verifier.candidate.query_loop
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (concreteCandidateQueryOps rest) proof p a g obs geometry b)
      proof p a g obs geometry b 22#usize = .ok (.Ok (out,bout))) :
    ∀ k : Fin 12, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
      a0.next.val=10+k.val ∧
      verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
        proof p a0 g obs geometry b0=.ok (.Ok (a1,b1)) ∧
      AspisR1S4TwelveQueryFieldResultsRootV1.QueryFieldEvidence concreteOps proof p g a0 := by
  let call : QueryCall := fun proof p a g obs geometry b =>
    verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest) proof p a g obs geometry b
  have advance : ∀ a a1 b b1, call proof p a g obs geometry b=.ok (.Ok (a1,b1)) →
      a1.next.val=a.next.val+1 := by
    intro a a1 b b1 hc
    exact query_next aops (concreteCandidateQueryOps rest) proof p a a1 g obs geometry b b1 hc
  have chain := AspisR1Stage2.emitted_twelve_ordered_calls
    call proof p g obs geometry advance a out b bout hstart hloop
  intro k
  have hadv : ∀ a a1 b b1,
      Stage2ContinuationOwnedLoop.adapt (fun a b => call proof p a g obs geometry b) a b =
        .ok (.Ok (),a1,b1) → a1.next.val=a.next.val+1 := by
    intro a a1 b b1 hc
    exact advance a a1 b b1 (adapted_ok_inv _ a a1 b b1 hc)
  obtain ⟨a0,a1,b0,b1,hindex,hcall⟩ := AspisR1S4TwelveQueryFieldResultsRootV1.chain_call_at _ _ hadv chain k.val k.isLt
  have hc := adapted_ok_inv _ a0 a1 b0 b1 hcall
  exact ⟨a0,a1,b0,b1,by omega,hc,
    candidate_call_field_evidence aops rest proof p g obs geometry a0 a1 b0 b1
      gamma claimPowers hgamma hpowers hcaller hscan hc⟩

#print axioms candidate_ten_queries_have_actual_call_field_results
#print axioms candidate_twelve_queries_have_actual_call_field_results
end AspisR1S4CandidateLoopActualCallsV1

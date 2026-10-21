import S4Stage2QueryCallRefinementV1
import S4V10ConcreteQueryOpsBuilderV1
import S4TenQueryFieldResultsRootV1
import S4TwelveQueryFieldResultsRootV1
import S4ConcreteKernelOpsRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4CandidateLoopFieldTransportV1

open AspisR1Stage2
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsV10QueryOpsResultTransportV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1S4FullQueryValuesPrefixV1 (withS4Callbacks)

abbrev FullWide := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev ClaimE := AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE

private theorem candidate_query_step_refines_old
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b b1 : verifier.BatchedWeights) (a1 : verifier.Accumulator)
    (h : verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
      proof p a g obs geometry b = .ok (.Ok (a1,b1))) :
    verifier.candidate.queryWithOps aops (withOldModelDots concreteOps rest)
      proof p a g obs geometry b = .ok (.Ok (a1,b1)) := by
  exact concrete_candidate_query_refines_old_model aops rest proof p a g obs geometry b
    (.Ok (a1,b1)) h

theorem candidate_ten_loop_refines_old
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (hstart : a.next.val = 0)
    (hloop : verifier.candidate.query_loop
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (concreteCandidateQueryOps rest) proof p a g obs geometry b)
      proof p a g obs geometry b 10#usize = .ok (.Ok (out,bout))) :
    verifier.candidate.query_loop
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (withOldModelDots concreteOps rest) proof p a g obs geometry b)
      proof p a g obs geometry b 10#usize = .ok (.Ok (out,bout)) := by
  apply AspisR1S4Stage2QueryCallRefinementV1.query_loop_ten_success_refines
    (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
      (concreteCandidateQueryOps rest) proof p a g obs geometry b)
    (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
      (withOldModelDots concreteOps rest) proof p a g obs geometry b)
    proof p g obs geometry a out b bout
  · intro a a1 b b1 hc
    exact query_next aops (concreteCandidateQueryOps rest) proof p a a1 g obs geometry b b1 hc
  · intro a b a1 b1 hc
    exact candidate_query_step_refines_old aops rest proof p a g obs geometry b b1 a1 hc
  · exact hstart
  · exact hloop

theorem candidate_twelve_loop_refines_old
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (hstart : a.next.val = 10)
    (hloop : verifier.candidate.query_loop
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (concreteCandidateQueryOps rest) proof p a g obs geometry b)
      proof p a g obs geometry b 22#usize = .ok (.Ok (out,bout))) :
    verifier.candidate.query_loop
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (withOldModelDots concreteOps rest) proof p a g obs geometry b)
      proof p a g obs geometry b 22#usize = .ok (.Ok (out,bout)) := by
  apply AspisR1S4Stage2QueryCallRefinementV1.query_loop_twelve_success_refines
    (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
      (concreteCandidateQueryOps rest) proof p a g obs geometry b)
    (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
      (withOldModelDots concreteOps rest) proof p a g obs geometry b)
    proof p g obs geometry a out b bout
  · intro a a1 b b1 hc
    exact query_next aops (concreteCandidateQueryOps rest) proof p a a1 g obs geometry b b1 hc
  · intro a b a1 b1 hc
    exact candidate_query_step_refines_old aops rest proof p a g obs geometry b b1 a1 hc
  · exact hstart
  · exact hloop


theorem candidate_ten_queries_have_field_results
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (gamma : ClaimE)
    (claimPowers : Array ClaimE 29#usize)
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
      a0.next.val = k.val ∧
      verifier.candidate.queryWithOps aops
        (withS4Callbacks (install concreteOps) rest)
        proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) ∧
      AspisR1S4TwelveQueryFieldResultsRootV1.QueryFieldEvidence concreteOps proof p g a0 := by
  have hold := candidate_ten_loop_refines_old aops rest proof p g obs geometry
    a out b bout hstart hloop
  have hold' : verifier.candidate.query_loop
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (withS4Callbacks (install concreteOps) rest)
        proof p a g obs geometry b)
      proof p a g obs geometry b 10#usize = .ok (.Ok (out,bout)) := by
    simpa [withOldModelDots, oldModelDots, withS4Callbacks] using hold
  exact AspisR1S4TenQueryFieldResultsRootV1.ten_queries_have_field_results
    aops concreteOps rest proof p g obs geometry a out b bout gamma claimPowers
    hgamma hpowers hcaller hscan hstart hold'

theorem candidate_twelve_queries_have_field_results
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (gamma : ClaimE)
    (claimPowers : Array ClaimE 29#usize)
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
      a0.next.val = 10+k.val ∧
      verifier.candidate.queryWithOps aops
        (withS4Callbacks (install concreteOps) rest)
        proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) ∧
      AspisR1S4TwelveQueryFieldResultsRootV1.QueryFieldEvidence concreteOps proof p g a0 := by
  have hold := candidate_twelve_loop_refines_old aops rest proof p g obs geometry
    a out b bout hstart hloop
  have hold' : verifier.candidate.query_loop
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (withS4Callbacks (install concreteOps) rest)
        proof p a g obs geometry b)
      proof p a g obs geometry b 22#usize = .ok (.Ok (out,bout)) := by
    simpa [withOldModelDots, oldModelDots, withS4Callbacks] using hold
  exact AspisR1S4TwelveQueryFieldResultsRootV1.twelve_queries_have_field_results
    aops concreteOps rest proof p g obs geometry a out b bout gamma claimPowers
    hgamma hpowers hcaller hscan hstart hold'

end AspisR1S4CandidateLoopFieldTransportV1

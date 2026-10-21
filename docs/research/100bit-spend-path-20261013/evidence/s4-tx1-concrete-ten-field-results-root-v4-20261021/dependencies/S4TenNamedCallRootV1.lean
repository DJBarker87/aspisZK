import S4TenQueryFieldResultsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4TenNamedCallRootV1
open AspisR1Stage2 AspisR1S4FullQueryValuesPrefixV1 AspisR1S4TwelveQueryFieldResultsRootV1

def namedCall (aops : AccumulateOps)
    (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops) (rest : QueryOps) : QueryCall :=
  fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
    (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
    proof p a g obs geometry b

theorem ten_named_call_field_results
    (aops : AccumulateOps) (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops)
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (gamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE)
    (claimPowers : Array AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE 29#usize)
    (hgamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma=.ok claimPowers)
    (hcaller : fullArrayToCurrent g=AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers)
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true)
    (hstart : a.next.val=0)
    (hloop : verifier.candidate.query_loop
      (namedCall aops headOps rest)
      proof p a g obs geometry b 10#usize=.ok (.Ok (out,bout))) :
    ∀ k : Fin 10, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
      a0.next.val=k.val ∧
      verifier.candidate.queryWithOps aops
        (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
        proof p a0 g obs geometry b0=.ok (.Ok (a1,b1)) ∧
      QueryFieldEvidence headOps proof p g a0 := by
  exact AspisR1S4TenQueryFieldResultsRootV1.ten_queries_have_field_results
    aops headOps rest proof p g obs geometry a out b bout gamma claimPowers
    hgamma hpowers hcaller hscan hstart hloop

#print axioms ten_named_call_field_results
end AspisR1S4TenNamedCallRootV1

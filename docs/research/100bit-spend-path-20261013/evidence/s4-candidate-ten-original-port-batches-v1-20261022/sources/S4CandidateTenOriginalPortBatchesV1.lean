import S4CandidateLoopFieldTransportV1
import S4OriginalPortAcceptedQueryV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4CandidateTenOriginalPortBatchesV1
open AspisR1Stage2
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4CandidateLoopFieldTransportV1
open AspisR1.S4OriginalPortAcceptedQueryV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsV10QueryOpsResultTransportV1
open AspisR1.MixedLeafEncoding AspisR1.MixedLeafDecoder AspisR1

structure OriginalPortBatchEvidence
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (acc : verifier.Accumulator) (g : Array AspisR1S4FullQueryValuesPrefixV1.FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (pending : verifier.BatchedWeights) (gamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE) : Prop where
  witnesses :
    ∃ (i : Std.U32) (u : Std.Usize) (q : Slice U8) (dots : Array AspisR1S4FullQueryValuesPrefixV1.FullWide 4#usize)
      (a : Array U8 608#usize) (c1 : C1) (c2 : C2),
      Array.index_usize p.queries acc.next = .ok i ∧
      lift (UScalar.cast .Usize i) = .ok u ∧
      sourceOpening proof acc.next = .ok q ∧
      (withOldModelDots concreteOps rest).dots q g = .ok dots ∧
      a.val = q.val.slice 0 (608#usize) ∧
      decodeC1 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).take 480) = some c1 ∧
      decodeC2 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).drop 480) = some c2 ∧
      dots.val.map (fun x => AspisR1CurrentPreparedClaim.Concrete.decode
        (AspisR1S4P6PowersQueryJoinV1.stage2ToClaim x)) =
      List.ofFn (fun slot : Fin 4 => AspisV6Width29CorrelatedAgreement.width29Batch
        (AspisR1D18S4ConcreteWidth29KernelV1.localWord c1 c2 slot)
        (AspisR1CurrentPreparedClaim.Concrete.decode gamma))

private theorem scan_length (proof : Slice U8)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    proof.val.length = 57607 := by
  have hlen : Slice.len proof = 57607#usize := by
    by_cases heq : Slice.len proof = 57607#usize
    · exact heq
    · have hneq : (Slice.len proof != 57607#usize) = true := by simp [heq]
      have hfalse : MultiproofParserRef.parser_reference.scan proof = .ok false := by
        simp [MultiproofParserRef.parser_reference.scan, hneq]
      rw [hfalse] at hscan
      cases hscan
  have hv := congrArg UScalar.val hlen
  simpa [Slice.len, Slice.length] using hv

theorem candidate_ten_original_port_batches
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared)
    (g : Array AspisR1S4FullQueryValuesPrefixV1.FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (gamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE)
    (powers : Array AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE 29#usize)
    (hgamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers)
    (hcaller : AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
      AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast powers)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hstart : a.next.val = 0)
    (hloop : verifier.candidate.query_loop
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (concreteCandidateQueryOps rest) proof p a g obs geometry b)
      proof p a g obs geometry b 10#usize = .ok (.Ok (out,bout))) :
    ∀ j : Fin 10, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
      a0.next.val = j.val ∧
      verifier.candidate.queryWithOps aops (withOldModelDots concreteOps rest)
        proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) ∧
      OriginalPortBatchEvidence rest proof p a0 g obs geometry b0 gamma := by
  have hfields := candidate_ten_queries_have_field_results aops rest proof p g obs geometry
    a out b bout gamma powers hgamma hpowers hcaller hscan hstart hloop
  intro j
  obtain ⟨a0,a1,b0,b1,hcursor,hcall,_hevidence⟩ := hfields j
  have hcall' : verifier.candidate.queryWithOps aops (withOldModelDots concreteOps rest)
      proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) := by
    simpa [withOldModelDots, oldModelDots, withS4Callbacks] using hcall
  exact ⟨a0,a1,b0,b1,hcursor,hcall',⟨successful_query_has_exact_original_port_batches
    aops rest proof p a0 g obs geometry b0 (.Ok (a1,b1)) gamma powers hgamma hpowers hcaller
    (scan_length proof hscan) hscan hcall'⟩⟩

#print axioms candidate_ten_original_port_batches
end AspisR1S4CandidateTenOriginalPortBatchesV1

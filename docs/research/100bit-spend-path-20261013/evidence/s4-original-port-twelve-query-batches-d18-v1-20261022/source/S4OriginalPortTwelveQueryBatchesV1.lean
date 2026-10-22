import S4OriginalPortAcceptedQueryV1
import S4TwelveQueryFieldResultsRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1.S4OriginalPortTwelveQueryBatchesV1

open AspisR1Stage2
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsV10QueryOpsResultTransportV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4TwelveQueryFieldResultsRootV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1.S4OriginalPortAcceptedQueryV1
open AspisR1.MixedLeafEncoding AspisR1.MixedLeafDecoder

private def OriginalPortBatchEvidence
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared) (acc : verifier.Accumulator)
    (g : Array FullWide 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (gamma : ClaimE) : Prop :=
  ∃ (i : U32) (u : Usize) (q : Slice U8) (dots : Array FullWide 4#usize)
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

private theorem scanned_source_proof_length (proof : Slice U8)
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

/-- A successful twelve-query loop using the original P6-installed dots port
retains each reached callback result and its four exact local batch values.
The theorem is over the selected source-shaped Stage2 model; frozen Std and
caller installation remain separate boundaries. -/
theorem original_port_twelve_queries_have_exact_batches
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry)
    (acc out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (gamma : ClaimE) (powers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers)
    (hcaller : fullArrayToCurrent g = claimArrayToFast powers)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hstart : acc.next.val = 10)
    (hloop : verifier.candidate.query_loop
      (fun proof p acc g obs geometry b =>
        verifier.candidate.queryWithOps aops (withOldModelDots concreteOps rest)
          proof p acc g obs geometry b)
      proof p acc g obs geometry b 22#usize = .ok (.Ok (out,bout))) :
    ∀ k : Fin 12, ∃ (acc0 acc1 : verifier.Accumulator)
      (b0 b1 : verifier.BatchedWeights),
      acc0.next.val = 10+k.val ∧
      verifier.candidate.queryWithOps aops (withOldModelDots concreteOps rest)
        proof p acc0 g obs geometry b0 = .ok (.Ok (acc1,b1)) ∧
      OriginalPortBatchEvidence rest proof p acc0 g obs geometry b0 gamma := by
  have hloop' : verifier.candidate.query_loop
      (fun proof p acc g obs geometry b =>
        verifier.candidate.queryWithOps aops
          (withS4Callbacks
            (AspisR1FastDotsFourCallbacksForwardRootV1.install concreteOps) rest)
          proof p acc g obs geometry b)
      proof p acc g obs geometry b 22#usize = .ok (.Ok (out,bout)) := by
    simpa [withOldModelDots, oldModelDots, withS4Callbacks,
      AspisR1FastDotsV10QueryOpsResultTransportV1.oldModelDots] using hloop
  have hfields := twelve_queries_have_field_results aops concreteOps rest proof p g
    obs geometry acc out b bout gamma powers hgamma hpowers hcaller hscan hstart hloop'
  intro k
  obtain ⟨acc0,acc1,b0,b1,hcursor,hcall,_hfields⟩ := hfields k
  exact ⟨acc0,acc1,b0,b1,hcursor,hcall,
    successful_query_has_exact_original_port_batches aops rest proof p acc0 g obs
      geometry b0 (.Ok (acc1,b1)) gamma powers hgamma hpowers hcaller
      (scanned_source_proof_length proof hscan) hscan hcall⟩

#print axioms scanned_source_proof_length
#print axioms original_port_twelve_queries_have_exact_batches

end AspisR1.S4OriginalPortTwelveQueryBatchesV1

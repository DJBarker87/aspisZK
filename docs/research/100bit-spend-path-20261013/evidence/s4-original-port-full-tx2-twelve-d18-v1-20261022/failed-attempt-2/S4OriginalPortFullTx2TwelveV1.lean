import S4OriginalPortTwelveQueryBatchesV1
import S4ConcreteResumeTwelveFieldsRootV2

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1.S4OriginalPortFullTx2TwelveV1

open AspisR1Stage2
open AspisR1S4Tx2FullSourceOwnedCutV1
open AspisR1S4ConcreteResumeTwelveFieldsRootV2
open AspisR1S4FullTx2CandidateFieldsRootV1
open AspisR1S4P6PowersQueryJoinV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsV10QueryOpsResultTransportV1
open AspisR1.S4OriginalPortTwelveQueryBatchesV1
open AspisR1.S4OriginalPortAcceptedQueryV1
open AspisR1.MixedLeafEncoding AspisR1.MixedLeafDecoder

private def OriginalPortCall (aops : AccumulateOps) (rest : QueryOps) : AspisR1FastDotsTx2PowersQuerySourceCutV1.QueryCall :=
  fun proof p a g obs geometry pending =>
    verifier.candidate.queryWithOps aops (withOldModelDots concreteOps rest)
      proof p a g obs geometry pending

private def OriginalPortBatchEvidence
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (acc : verifier.Accumulator) (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (pending : verifier.BatchedWeights) (gamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE) : Prop :=
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

/-- Full tx2 source-cut success itself reaches the same original-port loop and
all twelve actual query calls, with canonical source powers tied to this
successful resume. `hscan` and the non-S4 operation/caller slots remain explicit. -/
theorem original_port_full_tx2_twelve_exact_batches {H : Type}
    (ops : Ops H) (aops : AccumulateOps) (rest : QueryOps)
    (inst : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : tx2CommonFullSourceCut (withS4SourceSlots (withConcreteResume ops))
      (OriginalPortCall aops rest) inst public_bytes proof checkpoint hash obs = .ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (acc : verifier.Accumulator)
      (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (acc1 : verifier.Accumulator) (pending1 : verifier.BatchedWeights)
      (powers : ClaimArray),
      verifier.resumeWithOps (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops.resumeOps)
        inst checkpoint proof public_bytes transport.Variant.S2 hash = .ok (.Ok (p,acc)) ∧
      acc.next = 10#usize ∧
      sourceP6WeightsPowers 29#usize p.gamma = .ok g ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize
        (stage2ToClaim p.gamma) = .ok powers ∧
      AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical (stage2ToClaim p.gamma) ∧
      fullArrayToCurrent g = claimArrayToFast powers ∧
      ops.forRange p.queries acc.next 22#usize = .ok (.Ok geometry) ∧
      ops.newPending (alloc.vec.Vec.deref acc.weights) = .ok (.Ok pending) ∧
      verifier.candidate.query_loop (OriginalPortCall aops rest) proof p acc g obs geometry
        pending 22#usize = .ok (.Ok (acc1,pending1)) ∧
      ∀ k : Fin 12, ∃ (acc0 acc2 : verifier.Accumulator)
        (b0 b1 : verifier.BatchedWeights),
        acc0.next.val = 10+k.val ∧
        verifier.candidate.queryWithOps aops (withOldModelDots concreteOps rest)
          proof p acc0 g obs geometry b0 = .ok (.Ok (acc2,b1)) ∧
        OriginalPortBatchEvidence rest proof p acc0 g obs geometry b0
          (stage2ToClaim p.gamma) := by
  have hcut := tx2CommonFullSourceCut_success_reaches_query_loop
    (withS4SourceSlots (withConcreteResume ops)) (OriginalPortCall aops rest)
    inst public_bytes proof checkpoint hash obs h
  obtain ⟨p,acc,g,geometry,pending,acc1,pending1,hresume,hsplit,hpow,hgeometry,
      hpending,hloop⟩ := hcut
  have hgammaRaw := AspisR1S4ResumeGammaActualCanonicalV1.resume_gamma_canonical
    ops.resumeOps inst checkpoint proof public_bytes transport.Variant.S2 hash p acc hresume
  have hgamma := raw_bounds_claim_canonical p.gamma hgammaRaw
  have hsource : sourceP6WeightsPowers 29#usize p.gamma = .ok g := by
    change sourceP6WeightsPowers 29#usize p.gamma = .ok g at hpow
    exact hpow
  obtain ⟨powers,hpowers,hcaller⟩ := source_powers_same_claim_array
    p.gamma g hgamma hsource
  have hstart : acc.next.val = 10 := by
    have hsplit' : acc.next = 10#usize := by
      simpa [withS4SourceSlots, withConcreteResume] using hsplit
    simpa using congrArg UScalar.val hsplit'
  have hqueries := original_port_twelve_queries_have_exact_batches
    aops rest proof p g obs geometry acc acc1 pending pending1
    (stage2ToClaim p.gamma) powers hgamma hpowers hcaller hscan hstart hloop
  refine ⟨p,acc,g,geometry,pending,acc1,pending1,powers,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hresume
  · exact hstart
  · exact hsource
  · exact hpowers
  · exact hgamma
  · exact hcaller
  · exact hgeometry
  · exact hpending
  · exact hloop
  · exact hqueries

#print axioms original_port_full_tx2_twelve_exact_batches

end AspisR1.S4OriginalPortFullTx2TwelveV1

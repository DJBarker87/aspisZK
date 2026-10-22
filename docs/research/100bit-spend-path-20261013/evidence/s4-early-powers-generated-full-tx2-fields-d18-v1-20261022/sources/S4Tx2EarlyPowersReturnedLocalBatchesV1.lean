import S4Tx2EarlyPowersCandidateFieldsD18V1
import S4ConcreteResumeTwelveFieldsRootV2
import S4QueryTypedOpeningV1
import S4QueryReturnedSemanticsV1
import S4ClaimPowersSemanticV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4Tx2EarlyPowersReturnedLocalBatchesV1
open AspisR1Stage2
open AspisR1S4Tx2FullSourceOwnedCutV1
open AspisR1S4P6PowersQueryJoinV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1S4Tx2EarlyPowersCandidateFieldsD18V1
open AspisR1S4ConcreteResumeTwelveFieldsRootV2
open AspisR1.S4QueryTypedOpeningV1
open AspisR1S4QueryReturnedSemanticsV1
open AspisR1.S4ClaimPowersSemanticV1
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsV10CandidateQueryFieldEvidenceV1
open AspisR1FastDotsV10CandidateQueryFullWideBoundsV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsTailFieldProductRootV1

/-- Same successful tx2 execution reaches all twelve actual generated-power
queries and attaches the decoded local first-fold batch result to each exact
returned callback array. The powers slot is the S1 generated early-return
candidate body, not an independently supplied P6 model success. -/
theorem full_tx2_earlypowers_twelve_actual_returned_local_batches {H : Type}
    (ops : Ops H) (aops : AccumulateOps) (rest : QueryOps)
    (inst : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : tx2CommonFullSourceCut
      (withS4SourceSlots (withConcreteResume ops))
      (candidateCall aops rest) inst public_bytes proof checkpoint hash obs = .ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (a : verifier.Accumulator)
      (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (powers : ClaimArray),
      let gamma := stage2ToClaim p.gamma
      verifier.resumeWithOps
        (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops.resumeOps)
        inst checkpoint proof public_bytes transport.Variant.S2 hash = .ok (.Ok (p,a)) ∧
      a.next = 10#usize ∧
      AspisR1S4EarlyPowersSourceBindingV1.extractedEarlyWeightsPowers
        29#usize p.gamma = .ok g ∧
      ops.forRange p.queries a.next 22#usize = .ok (.Ok geometry) ∧
      ops.newPending (alloc.vec.Vec.deref a.weights) = .ok (.Ok pending) ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers ∧
      ClaimCanonical gamma ∧
      AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g = claimArrayToFast powers ∧
      (∀ j : Fin 29,
        wideDecoded ((AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g).val[j.val]'(by scalar_tac)) =
          AspisR1CurrentPreparedClaim.Concrete.decode gamma ^ j.val) ∧
      (∀ k : Fin 12, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val = 10+k.val ∧
        candidateCall aops rest proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) ∧
        CandidateQueryReturnedLocalBatchEvidence rest proof p a0 g powers gamma) := by
  let rops := withConcreteResume ops
  obtain ⟨p,a,g,geometry,pending,powers,hresume,hstart,hpowers,hgeometry,hpending,
      hclaim,hmap,hqueries⟩ :=
    full_tx2_source_cut_success_twelve_actual_fields rops aops rest inst
      public_bytes proof checkpoint hash obs
      (hcanonical := by
        intro p a hresume
        have hraw := AspisR1S4ResumeGammaActualCanonicalV1.resume_gamma_canonical
          ops.resumeOps inst checkpoint proof public_bytes transport.Variant.S2 hash p a hresume
        exact raw_bounds_claim_canonical p.gamma hraw)
      (hscan := hscan) (h := h)
  let gamma := stage2ToClaim p.gamma
  have hraw := AspisR1S4ResumeGammaActualCanonicalV1.resume_gamma_canonical
    ops.resumeOps inst checkpoint proof public_bytes transport.Variant.S2 hash p a hresume
  have hgamma : ClaimCanonical gamma := by
    change AspisR1CurrentPreparedClaim.Concrete.Canonical (stage2ToClaim p.gamma)
    exact raw_bounds_claim_canonical p.gamma hraw
  have hsource :=
    AspisR1.S4ClaimPowersSemanticV1.caller_powers_exact
      (AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g) gamma powers
      hgamma hclaim hmap
  have hreturned : ∀ k : Fin 12,
      ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val = 10+k.val ∧
        candidateCall aops rest proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) ∧
        CandidateQueryReturnedLocalBatchEvidence rest proof p a0 g powers gamma := by
    intro k
    obtain ⟨a0,a1,b0,b1,hcursor,hcall,hevidence,_hbounds⟩ := hqueries k
    have htyped :=
      AspisR1.S4QueryTypedOpeningV1.candidate_fields_have_typed_opening
        rest proof p a0 g powers hscan hevidence
    have hlocal :=
      AspisR1S4QueryReturnedSemanticsV1.typed_opening_returned_local_batches
        rest proof p a0 g powers gamma hgamma hclaim htyped
    exact ⟨a0,a1,b0,b1,hcursor,hcall,hlocal⟩
  exact ⟨p,a,g,geometry,pending,powers,hresume,hstart,hpowers,hgeometry,hpending,
    hclaim,hgamma,hmap,hsource,hreturned⟩

#print axioms full_tx2_earlypowers_twelve_actual_returned_local_batches
end AspisR1S4Tx2EarlyPowersReturnedLocalBatchesV1

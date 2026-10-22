import S4Tx2TypedOpeningsV1
import S4ResumedPowersSemanticV1
import S4QueryReturnedSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4Tx2TwelveReturnedLocalBatchesV1

open AspisR1Stage2
open AspisR1S4Tx2FullSourceOwnedCutV1
open AspisR1.S4Tx2TypedOpeningsV1
open AspisR1.S4QueryTypedOpeningV1
open AspisR1S4FullTx2CandidateFieldsRootV1
  (candidateCall withS4SourceSlots)
open AspisR1S4P6PowersQueryJoinV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1S4ConcreteResumeTwelveFieldsRootV2
open AspisR1S4ResumeGammaActualCanonicalV1
open AspisR1.S4ResumedPowersSemanticV1
open AspisR1S4QueryReturnedSemanticsV1
open AspisR1FastDotsV10CandidateQueryFullWideBoundsV1
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsV10CandidateQueryFieldEvidenceV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsTailFieldProductRootV1

theorem full_tx2_twelve_actual_returned_local_batches {H : Type}
    (ops : Ops H) (aops : AccumulateOps) (rest : QueryOps)
    (inst : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : tx2CommonFullSourceCut (withS4SourceSlots (withConcreteResume ops))
      (candidateCall aops rest) inst public_bytes proof checkpoint hash obs = .ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (a : verifier.Accumulator)
      (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (powers : ClaimArray),
      let gamma := stage2ToClaim p.gamma
      verifier.resumeWithOps (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops.resumeOps)
        inst checkpoint proof public_bytes transport.Variant.S2 hash = .ok (.Ok (p,a)) ∧
      a.next = 10#usize ∧
      sourceP6WeightsPowers 29#usize p.gamma = .ok g ∧
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
  obtain ⟨p,a,g,geometry,pending,powers,hresume,ha,hpowers,hgeometry,hpending,
      hclaim,hmap,hqueries⟩ :=
    full_tx2_concrete_reader_twelve_typed_openings
      ops aops rest inst public_bytes proof checkpoint hash obs hscan h
  let gamma := stage2ToClaim p.gamma
  have hraw := resume_gamma_canonical ops.resumeOps inst checkpoint proof public_bytes
    transport.Variant.S2 hash p a hresume
  have hcanonical : ClaimCanonical gamma := raw_bounds_claim_canonical p.gamma hraw
  have hsource := same_resume_source_powers_exact ops inst checkpoint proof public_bytes
    hash p a g hresume hpowers
  have hreturned : ∀ k : Fin 12,
      ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val = 10+k.val ∧
        candidateCall aops rest proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) ∧
        CandidateQueryReturnedLocalBatchEvidence rest proof p a0 g powers gamma := by
    intro k
    obtain ⟨a0,a1,b0,b1,hcursor,hcall,htyped,_hbounds⟩ := hqueries k
    have hlocal := typed_opening_returned_local_batches rest proof p a0 g powers gamma
      hcanonical hclaim htyped
    exact ⟨a0,a1,b0,b1,hcursor,hcall,hlocal⟩
  exact ⟨p,a,g,geometry,pending,powers,hresume,ha,hpowers,hgeometry,hpending,
    hclaim,hcanonical,hmap,hsource,hreturned⟩

#print axioms full_tx2_twelve_actual_returned_local_batches

end AspisR1S4Tx2TwelveReturnedLocalBatchesV1

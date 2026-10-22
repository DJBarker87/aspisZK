import S4ConcreteResumeTwelveFieldsRootV2
import S4QueryTypedOpeningV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4Tx2TypedOpeningsV1
open AspisR1Stage2
open AspisR1S4P6PowersQueryJoinV1
open AspisR1FastDotsV10CandidateQueryFullWideBoundsV1
open AspisR1S4Tx2FullSourceOwnedCutV1
open AspisR1S4FullTx2CandidateFieldsRootV1
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1S4ConcreteResumeTwelveFieldsRootV2
open AspisR1.S4QueryTypedOpeningV1
attribute [local irreducible] verifier.candidate.query_loop verifier.candidate.queryWithOps
theorem full_tx2_concrete_reader_twelve_typed_openings {H : Type}
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
      verifier.resumeWithOps (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops.resumeOps)
        inst checkpoint proof public_bytes transport.Variant.S2 hash = .ok (.Ok (p,a)) ∧
      a.next = 10#usize ∧
      sourceP6WeightsPowers 29#usize p.gamma = .ok g ∧
      ops.forRange p.queries a.next 22#usize = .ok (.Ok geometry) ∧
      ops.newPending (alloc.vec.Vec.deref a.weights) = .ok (.Ok pending) ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize
        (stage2ToClaim p.gamma) = .ok powers ∧
      AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
        AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast powers ∧
      (∀ k : Fin 12, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val = 10+k.val ∧
        candidateCall aops rest proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) ∧
        CandidateQueryTypedOpeningEvidence rest proof p a0 g powers ∧
        ∃ (q : Slice U8) (values : Array FullWide 4#usize),
          AspisR1S4FullQueryValuesPrefixV1.sourceOpening proof a0.next = .ok q ∧
          (concreteCandidateQueryOps rest).dots q g = .ok values ∧
          (∀ x ∈ values.val, FullCoordinateBound x)) := by
  obtain ⟨p,a,g,geometry,pending,powers,hresume,ha,hpowers,hgeometry,hpending,hclaim,hmap,hqueries⟩ :=
    full_tx2_concrete_reader_twelve_actual_fields ops aops rest inst public_bytes proof checkpoint hash obs hscan h
  refine ⟨p,a,g,geometry,pending,powers,hresume,ha,hpowers,hgeometry,hpending,hclaim,hmap,?_⟩
  intro k
  obtain ⟨a0,a1,b0,b1,hcursor,hcall,hfields,hbounds⟩ := hqueries k
  exact ⟨a0,a1,b0,b1,hcursor,hcall,
    AspisR1.S4QueryTypedOpeningV1.candidate_fields_have_typed_opening rest proof p a0 g powers hscan hfields,
    hbounds⟩
#print axioms full_tx2_concrete_reader_twelve_typed_openings
end AspisR1.S4Tx2TypedOpeningsV1

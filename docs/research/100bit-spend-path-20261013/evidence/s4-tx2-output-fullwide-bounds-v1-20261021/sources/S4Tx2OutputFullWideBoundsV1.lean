import S4Tx2ResumeTwelveFieldEvidenceV2
import S4V10CandidateQueryFullWideBoundsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4Tx2OutputFullWideBoundsV1

open AspisR1Stage2
open AspisR1S4Tx2ResumeTwelveFieldEvidenceV2
open AspisR1S4P6PowersQueryJoinV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
  (ClaimE ClaimCanonical claimArrayToFast)
open AspisR1FastDotsV10CandidateQueryFieldEvidenceV1
  (CandidateQueryFieldEvidence)
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1 (concreteCandidateQueryOps)
open AspisR1FastDotsV10CandidateQueryFullWideBoundsV1
  (FullCoordinateBound FullWide)

/-- For the twelve actual candidate queries reached after tx2 resume, preserve
    each same-call field-evidence witness and strengthen it with the eight
    explicit U32 coordinate bounds on the exact returned Stage2 FullWide
    array. This adds no independent query, callback, or range premise. -/
theorem tx2_after_resume_candidate_twelve_fullwide_coordinate_bounds
    {H : Type}
    (ops : AspisR1S4Tx2ResumeTwelveFieldEvidenceV2.ClaimOps H) (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (resumeResult : Result ResumeValue)
    (out : Accumulator) (bout : BatchWeights)
    (hcanonical : ∀ p a, resumeResult = .ok (.Ok (p,a)) →
      AspisR1CurrentPreparedClaim.Concrete.Canonical (stage2ToClaim p.gamma))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : tx2AfterResume resumeResult ops
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (concreteCandidateQueryOps rest) proof p a g obs geometry b)
      proof hash obs = .ok (.Ok (.Ok (out,bout)))) :
    ∃ p a g geometry pending claimPowers,
      resumeResult = .ok (.Ok (p,a)) ∧ a.next.val=10 ∧
      sourceP6WeightsPowers 29#usize p.gamma = .ok g ∧
      (withSourceP6WeightsPowers ops).makeGeometry p.queries a.next 22#usize = .ok geometry ∧
      (withSourceP6WeightsPowers ops).makePending (alloc.vec.Vec.deref a.weights) = .ok pending ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize
        (stage2ToClaim p.gamma) = .ok claimPowers ∧
      fullArrayToCurrent g = claimArrayToFast claimPowers ∧
      (∀ k : Fin 12, ∃ (a0 a1 : Accumulator) (b0 b1 : BatchWeights)
        (q : Slice U8)
        (values : Array AspisR1FastDotsV10CandidateQueryFullWideBoundsV1.FullWide 4#usize),
        a0.next.val=10+k.val ∧
        verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
          proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) ∧
        sourceOpening proof a0.next = .ok q ∧
        (concreteCandidateQueryOps rest).dots q g = .ok values ∧
        (∀ x ∈ values.val, FullCoordinateBound x)) := by
  obtain ⟨p,a,g,geometry,pending,claimPowers,hresume,hstart,hg,hgeometry,
    hpending,hpowers,hcaller,hslots⟩ :=
    tx2_after_resume_candidate_twelve_actual_fields ops aops rest proof hash obs
      resumeResult out bout hcanonical hscan h
  refine ⟨p,a,g,geometry,pending,claimPowers,hresume,hstart,hg,hgeometry,
    hpending,hpowers,hcaller,?_⟩
  intro k
  obtain ⟨a0,a1,b0,b1,hindex,hcall,hevidence⟩ := hslots k
  obtain ⟨_,_,q,values,hopening,hdots,hbounds⟩ :=
    AspisR1FastDotsV10CandidateQueryFullWideBoundsV1.candidate_query_fullwide_coordinate_bounds
      rest proof p a0 g claimPowers hevidence
  exact ⟨a0,a1,b0,b1,q,values,hindex,hcall,hopening,hdots,hbounds⟩

#print axioms tx2_after_resume_candidate_twelve_fullwide_coordinate_bounds

end AspisR1S4Tx2OutputFullWideBoundsV1

import S4P6PowersQueryJoinV1
import S4TwelveQueryFieldResultsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4EarlyPowersPrefixTwelveFieldsRootV1
open AspisR1Stage2
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4TwelveQueryFieldResultsRootV1
open AspisR1S4P6PowersQueryJoinV1

/-- Carrier transport of the existing transparent extracted indexed early
powers implementation used by ClaimPowers. This is the proposed source
replacement, not an assertion about original Rust Std from_fn. -/
def candidateEarlyWeightsPowers (_N : Usize) (x : Stage2Wide) : Result Stage2Array := do
  let values ← AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize (stage2ToClaim x)
  .ok (claimArrayToStage2 values)

def withCandidateEarlyWeightsPowers {H : Type} (ops : ClaimOps H) : ClaimOps H :=
  {ops with weightsPowers := candidateEarlyWeightsPowers}

private theorem bind_ok_inv {A B : Type} {r : Result A} {k : A → Result B} {out : B}
    (h : (do let x ← r; k x) = .ok out) : ∃ x, r = .ok x ∧ k x = .ok out := by
  cases r with
  | fail e => simp at h
  | div => simp at h
  | ok x => exact ⟨x,rfl,h⟩

theorem candidate_prefix_same_g {H : Type}
    (ops : ClaimOps H) (call : AspisR1FastDotsTx2PowersQuerySourceCutV1.QueryCall)
    (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (out : AspisR1FastDotsTx2PowersQuerySourceCutV1.QueryState)
    (h : AspisR1FastDotsTx2PowersQuerySourceCutV1.tx2QueryPrefix
      (withCandidateEarlyWeightsPowers ops) call proof p a hash obs=.ok out) :
    ∃ g : Stage2Array,
      candidateEarlyWeightsPowers 29#usize p.gamma=.ok g ∧
      ∃ geometry : verifier.QueryGeometry,
        (withCandidateEarlyWeightsPowers ops).makeGeometry p.queries a.next 22#usize=.ok geometry ∧
      ∃ pending : verifier.BatchedWeights,
        (withCandidateEarlyWeightsPowers ops).makePending (alloc.vec.Vec.deref a.weights)=.ok pending ∧
        verifier.candidate.query_loop call proof p a g obs geometry pending 22#usize=.ok out ∧
      ∃ claimPowers : ClaimArray,
        AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize (stage2ToClaim p.gamma)=.ok claimPowers ∧
        fullArrayToCurrent g=AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers := by
  obtain ⟨g,hg,geometry,hgeometry,pending,hpending,hloop⟩ :=
    AspisR1FastDotsTx2PowersQuerySourceCutV1.tx2_query_prefix_success_same_g
      (withCandidateEarlyWeightsPowers ops) call proof p a hash obs h
  have hearly : candidateEarlyWeightsPowers 29#usize p.gamma=.ok g := hg
  unfold candidateEarlyWeightsPowers at hearly
  obtain ⟨values,hvalues,hmap⟩ := bind_ok_inv hearly
  have hcaller : fullArrayToCurrent g=
      AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast values := by
    have hgmap : claimArrayToStage2 values=g := Result.ok.inj hmap
    rw [← hgmap]
    apply Subtype.ext
    change (values.val.map claimToStage2).map fullWideToCurrent =
      values.val.map AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimToFast
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    cases x <;> rfl
  exact ⟨g,hg,geometry,hgeometry,pending,hpending,hloop,values,hvalues,hcaller⟩

/-- The complete tx2 prefix supplies the actual same coefficient array and
successful query loop. No powers-success, coefficient-array equality or
individual query-success premise is independently supplied. -/
theorem early_prefix_twelve_field_results {H : Type}
    (ops : ClaimOps H) (aops : AccumulateOps)
    (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (bout : verifier.BatchedWeights) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (hgamma : AspisR1CurrentPreparedClaim.Concrete.Canonical (stage2ToClaim p.gamma))
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true)
    (hstart : a.next.val=10)
    (h : AspisR1FastDotsTx2PowersQuerySourceCutV1.tx2QueryPrefix
      (withCandidateEarlyWeightsPowers ops)
      (fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
        (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
        proof p a g obs geometry b)
      proof p a hash obs=.ok (.Ok (out,bout))) :
    ∃ g : Array FullWide 29#usize,
      candidateEarlyWeightsPowers 29#usize p.gamma=.ok g ∧
      ∃ geometry : verifier.QueryGeometry,
      (withCandidateEarlyWeightsPowers ops).makeGeometry p.queries a.next 22#usize=.ok geometry ∧
      ∀ k : Fin 12, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val=10+k.val ∧
        verifier.candidate.queryWithOps aops
          (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install headOps) rest)
          proof p a0 g obs
          geometry b0
          =.ok (.Ok (a1,b1)) ∧
        QueryFieldEvidence headOps proof p g a0 := by
  obtain ⟨g,hg,geometry,hgeometry,pending,hpending,hloop,claimPowers,hpowers,hcaller⟩ :=
    candidate_prefix_same_g ops _ proof p a hash obs (.Ok (out,bout)) h
  refine ⟨g,hg,geometry,hgeometry,?_⟩
  exact twelve_queries_have_field_results aops headOps rest proof p g obs geometry
    a out pending bout (stage2ToClaim p.gamma) claimPowers hgamma hpowers hcaller
    hscan hstart hloop

#print axioms candidate_prefix_same_g
#print axioms early_prefix_twelve_field_results
end AspisR1S4EarlyPowersPrefixTwelveFieldsRootV1

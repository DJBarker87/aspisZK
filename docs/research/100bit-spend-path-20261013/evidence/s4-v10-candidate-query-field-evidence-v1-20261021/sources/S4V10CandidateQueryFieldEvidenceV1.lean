import S4V10CallbackOutputFieldResultsV1
import S4FullQueryValuesPrefixV1
import S4OpeningBytesFromCurrentV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsV10CandidateQueryFieldEvidenceV1

open AspisR1Stage2
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsV10CallbackOutputFieldResultsV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1S4FullQueryValuesPrefixV1 (sourceOpening)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
  (ClaimE ClaimCanonical claimArrayToFast)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)

/-- Evidence carried by one successful candidate query: the actual reached
query/dots callback result is retained, and the Current-carrier values are
shown to represent that same returned candidate array. -/
def CandidateQueryFieldEvidence
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
    (claimPowers : Array ClaimE 29#usize) : Prop :=
  ∃ (i : U32) (u : Usize) (q : Slice U8)
    (candidateValues : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 4#usize)
    (currentValues : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 4#usize)
    (arrayQ : Array U8 608#usize)
    (v0 v1 v2 v3 : AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact),
    Array.index_usize p.queries a.next = .ok i ∧
    lift (UScalar.cast .Usize i) = .ok u ∧
    sourceOpening proof a.next = .ok q ∧
    q.val = proof.val.slice (10055 + a.next.val * 832)
      (10055 + a.next.val * 832 + 832) ∧
    (concreteCandidateQueryOps rest).dots q g = .ok candidateValues ∧
    currentArrayToFull currentValues = candidateValues ∧
    arrayQ.val = q.val.slice 0 (608#usize) ∧
    (∀ x ∈ currentValues.val,
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
    currentValues.val = [v0,v1,v2,v3] ∧
    LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      arrayQ (claimArrayToFast claimPowers) 0#usize v0 ∧
    LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      arrayQ (claimArrayToFast claimPowers) 1#usize v1 ∧
    LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      arrayQ (claimArrayToFast claimPowers) 2#usize v2 ∧
    LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      arrayQ (claimArrayToFast claimPowers) 3#usize v3

private theorem query_index_success_bound {α : Type} {n : Usize}
    (xs : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize xs i = .ok x) : i.val < n.val := by
  have hlen : i.val < xs.val.length := by
    by_contra hnot
    have hnone : xs[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa [xs.property] using hlen

private theorem scanned_proof_length (proof : Slice U8)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    proof.val.length = 57607 := by
  have hlen : Slice.len proof = 57607#usize := by
    by_cases hlen : Slice.len proof = 57607#usize
    · exact hlen
    · have hneq : (Slice.len proof != 57607#usize) = true := by simp [hlen]
      have hfalse : MultiproofParserRef.parser_reference.scan proof = .ok false := by
        simp [MultiproofParserRef.parser_reference.scan, hneq]
      rw [hfalse] at hscan
      cases hscan
  have hv := congrArg UScalar.val hlen
  simpa [Slice.len, Slice.length] using hv

/-- A successful complete candidate query provides an actual reached query
slice and dots result. The same strict scanner result supplies the proof length;
the emitted opening reader equation supplies the precise 832-byte query slice.
The callback-output theorem then gives canonical literal field evidence for
these very returned candidate dots, with the coefficient array identified by
the caller's single `fullArrayToCurrent` equality. -/
theorem candidate_query_success_field_evidence
    (aops : AccumulateOps) (rest : QueryOps) (proof : Slice U8)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (out : core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
      verifier.Error)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma =
      .ok claimPowers)
    (hcaller : fullArrayToCurrent g = claimArrayToFast claimPowers)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hquery : verifier.candidate.queryWithOps aops
      (concreteCandidateQueryOps rest) proof p a g obs geometry pending = .ok out) :
    CandidateQueryFieldEvidence rest proof p a g claimPowers := by
  obtain ⟨i,u,q,candidateValues,hi,hu,hopening,hdots⟩ :=
    full_query_values_success_prefix aops (concreteCandidateQueryOps rest)
      proof p a g obs geometry pending out hquery
  have hopening' : sourceOpening proof a.next = .ok q := by
    simpa [concreteCandidateQueryOps,
      AspisR1FastDotsV10QueryOpsResultTransportV1.withLiteralDots] using hopening
  have hj : a.next.val < 22 := by
    have hb := query_index_success_bound p.queries a.next i hi
    simpa using hb
  have hlen := scanned_proof_length proof hscan
  obtain ⟨q', hq', hread'⟩ :=
    AspisR1S4OpeningBytesFromCurrentV1.opening_slice_exact proof a.next
      hj (by omega : 28359 ≤ proof.val.length)
  have hqeq : q' = q := Result.ok.inj (hq'.symm.trans hopening')
  have hread : q.val = proof.val.slice
      (10055 + a.next.val * 832) (10055 + a.next.val * 832 + 832) := by
    simpa [hqeq] using hread'
  have hcall : (concreteCandidateQueryOps rest).dots q g = .ok candidateValues := by
    change (concreteCandidateQueryOps rest).dots q g = .ok candidateValues
    exact hdots
  obtain ⟨currentValues,arrayQ,v0,v1,v2,v3,hvalues,ha,hcanonical,hlist,hf0,hf1,hf2,hf3⟩ :=
    concrete_candidate_dots_success_has_endpoint_fields rest proof a.next.val q g
      gamma claimPowers hgamma hpowers hcaller hlen hj hread hscan candidateValues hcall
  exact ⟨i,u,q,candidateValues,currentValues,arrayQ,v0,v1,v2,v3,
    hi,hu,hopening',hread,hcall,hvalues,ha,hcanonical,hlist,hf0,hf1,hf2,hf3⟩

#print axioms query_index_success_bound
#print axioms scanned_proof_length
#print axioms candidate_query_success_field_evidence

end AspisR1FastDotsV10CandidateQueryFieldEvidenceV1

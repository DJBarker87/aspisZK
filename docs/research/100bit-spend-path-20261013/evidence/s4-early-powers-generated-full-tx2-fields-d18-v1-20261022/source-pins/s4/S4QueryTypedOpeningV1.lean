import S4V10CandidateQueryFieldEvidenceV1
import S4ScannedOpeningDecodeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4QueryTypedOpeningV1
open AspisR1Stage2
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsV10CallbackOutputFieldResultsV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1S4FullQueryValuesPrefixV1 (sourceOpening)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
  (ClaimE ClaimCanonical claimArrayToFast)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)

open AspisR1FastDotsV10CandidateQueryFieldEvidenceV1
def CandidateQueryTypedOpeningEvidence
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
    (claimPowers : Array ClaimE 29#usize) : Prop :=
  ∃ (i : U32) (u : Usize) (q : Slice U8)
    (candidateValues : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 4#usize)
    (currentValues : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 4#usize)
    (arrayQ : Array U8 608#usize)
    (v0 v1 v2 v3 : AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact) (c1 : AspisR1.MixedLeafEncoding.C1) (c2 : AspisR1.MixedLeafEncoding.C2),
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
      arrayQ (claimArrayToFast claimPowers) 3#usize v3 ∧
    AspisR1.MixedLeafDecoder.decodeC1 ((arrayQ.val.map AspisR1.ExtractedRecordByteValue.rawByte).take 480) = some c1 ∧
    AspisR1.MixedLeafDecoder.decodeC2 ((arrayQ.val.map AspisR1.ExtractedRecordByteValue.rawByte).drop 480) = some c2 ∧
    arrayQ.val.map AspisR1.ExtractedRecordByteValue.rawByte =
      AspisR1.MixedLeafEncoding.encodeC1 c1 ++ AspisR1.MixedLeafEncoding.encodeC2 c2

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


/-- Preserve the same source query, callback output and four literal field
results while deriving typed C1/C2 from the same scanned opening. -/
theorem candidate_fields_have_typed_opening (rest : QueryOps) (proof : Slice U8)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
    (powers : Array ClaimE 29#usize)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (he : CandidateQueryFieldEvidence rest proof p a g powers) :
    CandidateQueryTypedOpeningEvidence rest proof p a g powers := by
  rcases he with ⟨i,u,q,values,current,arrayQ,v0,v1,v2,v3,
    hi,hu,hopening,hread,hdots,hcurrent,ha,hcanonical,hlist,hf0,hf1,hf2,hf3⟩
  have hj : a.next.val < 22 := query_index_success_bound p.queries a.next i hi
  obtain ⟨c1,c2,hc1,hc2,hbytes⟩ := S4ScannedOpeningDecodeV1.scanned_opening_decode
    proof a.next.val q arrayQ (scanned_proof_length proof hscan) hj hread hscan ha
  exact ⟨i,u,q,values,current,arrayQ,v0,v1,v2,v3,c1,c2,
    hi,hu,hopening,hread,hdots,hcurrent,ha,hcanonical,hlist,hf0,hf1,hf2,hf3,hc1,hc2,hbytes⟩
#print axioms query_index_success_bound
#print axioms scanned_proof_length
#print axioms candidate_fields_have_typed_opening
end AspisR1.S4QueryTypedOpeningV1

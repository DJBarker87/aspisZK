import S4V10ConcreteQueryOpsBuilderV1
import S4ConcreteV10CandidateEndpointV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsV10CallbackOutputFieldResultsV1

open AspisR1Stage2
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsV10QueryOpsResultTransportV1
  (fullArrayToV10 fullArrayToV10_map literalDots withLiteralDots)
open AspisR1S4FullQueryValuesPrefixV1 (currentArrayToFull)
open AspisR1FastDotsV10TypedInnerBodyOpsV1 (mapWideArray)
open AspisR1FastDotsV10CarrierMapV1 (V10Wide)
open AspisR1FastDotsV10LiteralOuterTransferRootV1 (literalV10Outer)
open AspisR1S4FourWrapperCarrierTransportRootV1 (mapArray)
open AspisR1FastDotsV10CarrierMapV1 (wideToEbyK)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
  (ClaimE ClaimCanonical claimArrayToFast)

private theorem bind_ok_inv {α β : Type} {r : Result α}
    {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- A successful result from the concrete candidate callback is the same
four-value result certified by the scanner-derived endpoint theorem. This
uses the same coefficient array and concrete operations, and derives each
field witness from the strict scan rather than assuming an old/P6 callback
success. -/
theorem concrete_candidate_dots_success_has_endpoint_fields
    (rest : QueryOps) (proof : Slice U8) (j : Nat) (q : Slice U8)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma =
      .ok claimPowers)
    (hcaller : AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
      claimArrayToFast claimPowers)
    (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (candidateValues : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 4#usize)
    (hcall : (concreteCandidateQueryOps rest).dots q g = .ok candidateValues) :
    ∃ (currentValues : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 4#usize)
      (a : Array Std.U8 608#usize)
      (v0 v1 v2 v3 : AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact),
      currentArrayToFull currentValues = candidateValues ∧
      a.val = q.val.slice 0 (608#usize) ∧
      (∀ x ∈ currentValues.val,
        AspisR1CurrentWide.Proof.CanonicalWide
          (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      currentValues.val = [v0,v1,v2,v3] ∧
      AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
        (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (claimArrayToFast claimPowers) 0#usize v0 ∧
      AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
        (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (claimArrayToFast claimPowers) 1#usize v1 ∧
      AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
        (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (claimArrayToFast claimPowers) 2#usize v2 ∧
      AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
        (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (claimArrayToFast claimPowers) 3#usize v3 := by
  have hcall' : literalDots concreteOps q g = .ok candidateValues := by
    change (withLiteralDots concreteOps rest).dots q g = .ok candidateValues at hcall
    simpa only [withLiteralDots] using hcall
  have hcallerMapped : mapWideArray (fullArrayToV10 g) = claimArrayToFast claimPowers := by
    rw [fullArrayToV10_map]
    exact hcaller
  obtain ⟨literalValues,currentValues,a,v0,v1,v2,v3,hliteral,hcurrent,hmap,ha,hcanonical,hvals,hf0,hf1,hf2,hf3⟩ :=
    AspisR1FastDotsConcreteV10CandidateEndpointV1.concrete_literal_outer_total_and_field_results_from_scan
      proof j q (fullArrayToV10 g) gamma claimPowers hgamma hpowers hcallerMapped
      hlen hj hread hscan
  rw [concrete_candidate_dots_is_literal_v10 q g] at hcall'
  obtain ⟨calledValues,hcalled,hresult⟩ := bind_ok_inv hcall'
  have hsame : calledValues = literalValues :=
    Result.ok.inj (hcalled.symm.trans hliteral)
  have hresult' : currentArrayToFull (mapArray wideToEbyK literalValues) = candidateValues := by
    rw [← hsame]
    exact Result.ok.inj hresult
  have hbridge : currentArrayToFull currentValues = candidateValues := by
    rw [← hmap]
    exact hresult'
  have hf0' : AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      a (claimArrayToFast claimPowers) 0#usize v0 := by
    rw [← hcallerMapped]
    exact hf0
  have hf1' : AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      a (claimArrayToFast claimPowers) 1#usize v1 := by
    rw [← hcallerMapped]
    exact hf1
  have hf2' : AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      a (claimArrayToFast claimPowers) 2#usize v2 := by
    rw [← hcallerMapped]
    exact hf2
  have hf3' : AspisR1FastDotsLiteralCallbackValueRootV1.LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      a (claimArrayToFast claimPowers) 3#usize v3 := by
    rw [← hcallerMapped]
    exact hf3
  exact ⟨currentValues,a,v0,v1,v2,v3,hbridge,ha,hcanonical,hvals,hf0',hf1',hf2',hf3'⟩

#print axioms concrete_candidate_dots_success_has_endpoint_fields

end AspisR1FastDotsV10CallbackOutputFieldResultsV1

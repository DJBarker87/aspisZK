import S4V10DeadArrayFromFnSlotV1
import S4V10CountSlotIrrelevanceV1
import S4ConcreteV10CandidateEndpointV1
import S4V10ConcreteQueryOpsBuilderV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace AspisR1S4V10NoFromFnKernelRootV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsV10LiteralOuterTransferRootV1 (literalV10Outer)
open AspisR1S4FourWrapperCarrierTransportRootV1 (mapArray)
open AspisR1FastDotsV10TypedInnerBodyOpsV1 (mapWideArray)
open AspisR1FastDotsV10CarrierMapV1 (V10Wide)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)

/-- The two unused original-source slots diverge if invoked. The following
all-Result equality proves the actual candidate execution does not need either. -/
def noArrayOps : AspisR1FastDotsCurrent.FourDotsOps :=
  { concreteOps with arrayFromFn := fun {T F} _ _ _ => .div }
def noFromFnOps : AspisR1FastDotsCurrent.FourDotsOps :=
  { noArrayOps with wideLimbCount := .div }

theorem no_from_fn_outer_eq (q : Slice U8) (g : Array V10Wide 29#usize) :
    literalV10Outer noFromFnOps q g = literalV10Outer concreteOps q g := by
  calc
    literalV10Outer noFromFnOps q g = literalV10Outer noArrayOps q g :=
      AspisR1S4V10CountSlotIrrelevanceV1.literal_outer_independent_wide_limb_count
        noArrayOps .div q g
    _ = literalV10Outer concreteOps q g :=
      AspisR1FastDotsV10DeadArrayFromFnSlotV1.literalV10Outer_arrayFromFn_irrelevant
        concreteOps noArrayOps q g

theorem no_from_fn_outer_total_and_field_results_from_scan
    (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8)
    (input : Array V10Wide 29#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : mapWideArray input = claimArrayToFast claimPowers)
    (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    ∃ (literalValues : Array V10Wide 4#usize) (currentValues : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 4#usize)
      (a : Array Std.U8 608#usize) (v0 v1 v2 v3 : AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact),
      literalV10Outer noFromFnOps q input = .ok literalValues ∧
      mapArray
        AspisR1FastDotsV10CarrierMapV1.wideToEbyK literalValues = currentValues ∧
      a.val = q.val.slice 0 (608#usize) ∧
      (∀ x ∈ currentValues.val,
        AspisR1CurrentWide.Proof.CanonicalWide
          (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      currentValues.val = [v0,v1,v2,v3] ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (mapWideArray input) 0#usize v0 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (mapWideArray input) 1#usize v1 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (mapWideArray input) 2#usize v2 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (mapWideArray input) 3#usize v3 := by
  obtain ⟨literalValues,currentValues,a,v0,v1,v2,v3,hliteral,_hfixed,hmap,ha,hcanonical,hvalues,h0,h1,h2,h3⟩ :=
    AspisR1FastDotsConcreteV10CandidateEndpointV1.concrete_literal_outer_total_and_field_results_from_scan
      proof j q input gamma claimPowers hgamma hpowers hcaller hlen hj hread hscan
  refine ⟨literalValues,currentValues,a,v0,v1,v2,v3,?_,hmap,ha,hcanonical,hvalues,h0,h1,h2,h3⟩
  rw [no_from_fn_outer_eq]
  exact hliteral

/-- Callback semantics with no P6 array interpretation in the executed record. -/
def noFromFnDots (q : Slice U8)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize) :
    Result (Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 4#usize) := do
  let values ← literalV10Outer noFromFnOps q
    (AspisR1FastDotsV10QueryOpsResultTransportV1.fullArrayToV10 g)
  ok (AspisR1S4FullQueryValuesPrefixV1.currentArrayToFull
    (mapArray AspisR1FastDotsV10CarrierMapV1.wideToEbyK values))

theorem no_from_fn_dots_eq_concrete (rest : AspisR1Stage2.QueryOps)
    (q : Slice U8) (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize) :
    noFromFnDots q g =
      (AspisR1FastDotsV10ConcreteQueryOpsBuilderV1.concreteCandidateQueryOps rest).dots q g := by
  unfold noFromFnDots
  rw [no_from_fn_outer_eq]
  rfl

#print axioms no_from_fn_outer_eq
#print axioms no_from_fn_outer_total_and_field_results_from_scan
#print axioms no_from_fn_dots_eq_concrete
end AspisR1S4V10NoFromFnKernelRootV1

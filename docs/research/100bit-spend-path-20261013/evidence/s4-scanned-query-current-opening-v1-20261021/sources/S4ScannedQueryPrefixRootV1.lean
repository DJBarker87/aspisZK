import S4ScannedAcceptedRunRootV1
import AspisR1QueryPrefixToCurrentFourDotsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsScannedQueryPrefixRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1FastDotsForwardLiteralValueRootV1 (literalOps)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)
open AspisR1QueryPrefixToCurrentFourDotsV1

theorem scanned_query_prefix_success_literal_values
    (openingOp : PrefixOpeningOp) (base : Ops) (proof : Slice Std.U8)
    (p : AspisR1Stage2QueryTailCut.verifier.Prepared)
    (acc : AspisR1Stage2QueryTailCut.verifier.Accumulator)
    (g : Array PrefixWide 29#usize)
    (obs : Option (AspisR1Stage2QueryTailCut.verifier.Phase → Result Unit))
    (geometry : AspisR1Stage2QueryTailCut.verifier.QueryGeometry)
    (pending : AspisR1Stage2QueryTailCut.verifier.BatchedWeights)
    (out : core.result.Result
      (Std.Usize × Std.Usize × Slice Std.U8 × Array PrefixWide 4#usize)
      AspisR1Stage2QueryTailCut.verifier.Error)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : prefixArrayToCurrent g = claimArrayToFast claimPowers)
    (hlen : proof.val.length=57607) (hnext : acc.next.val<22)
    (hopening : ∀ q, openingOp proof acc.next=.ok q →
      q.val=proof.val.slice (10055+acc.next.val*832) (10055+acc.next.val*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true)
    (hactual : AspisR1Stage2QueryTailCut.query_values_forward_prefix_ops
      openingOp (currentFourDotsAsPrefix (install base)) proof p acc g obs geometry pending=.ok out) :
    ∃ (i : Std.U32) (u : Std.Usize) (q : Slice Std.U8)
      (dots : Array Wide 4#usize) (arrayQ : Array Std.U8 608#usize)
      (v0 v1 v2 v3 : Wide),
      Array.index_usize p.queries acc.next=.ok i ∧
      lift (UScalar.cast .Usize i)=.ok u ∧
      openingOp proof acc.next=.ok q ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots (install base) q (prefixArrayToCurrent g)=.ok dots ∧
      out=core.result.Result.Ok (acc.next,u,q,currentArrayToPrefix dots) ∧
      arrayQ.val=q.val.slice 0 (608#usize) ∧
      (∀ x∈dots.val,AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      dots.val=[v0,v1,v2,v3] ∧
      LiteralFieldResult (literalOps base) arrayQ (prefixArrayToCurrent g) 0#usize v0 ∧
      LiteralFieldResult (literalOps base) arrayQ (prefixArrayToCurrent g) 1#usize v1 ∧
      LiteralFieldResult (literalOps base) arrayQ (prefixArrayToCurrent g) 2#usize v2 ∧
      LiteralFieldResult (literalOps base) arrayQ (prefixArrayToCurrent g) 3#usize v3 := by
  obtain ⟨i,u,q,dots,hindex,hcast,hopen,hfour,hout⟩ :=
    query_values_forward_prefix_actual_s4 openingOp (install base) proof p acc g obs geometry pending out hactual
  obtain ⟨arrayQ,v0,v1,v2,v3,hprefix,hcanonical,hvals,h0,h1,h2,h3⟩ :=
    AspisR1FastDotsScannedAcceptedRunRootV1.scanned_accepted_run_literal_values
      base proof acc.next.val q (prefixArrayToCurrent g) dots gamma claimPowers
      hgamma hpowers hcaller hlen hnext (hopening q hopen) hscan hfour
  exact ⟨i,u,q,dots,arrayQ,v0,v1,v2,v3,hindex,hcast,hopen,hfour,hout,
    hprefix,hcanonical,hvals,h0,h1,h2,h3⟩

#print axioms scanned_query_prefix_success_literal_values
end AspisR1FastDotsScannedQueryPrefixRootV1

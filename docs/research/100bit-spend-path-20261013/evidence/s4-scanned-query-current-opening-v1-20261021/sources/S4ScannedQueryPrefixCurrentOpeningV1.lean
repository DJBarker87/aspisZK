import S4ScannedQueryPrefixRootV1
import S4OpeningBytesFromCurrentV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4ScannedQueryPrefixCurrentOpeningV1

open AspisR1FastDotsScannedQueryPrefixRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1QueryPrefixToCurrentFourDotsV1
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1FastDotsForwardLiteralValueRootV1 (literalOps)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

def actualOpeningOp : PrefixOpeningOp :=
  fun proof index => AspisR1Stage2.verifier.candidate.opening proof index

private theorem index_success_bound {α : Type} {n : Std.Usize}
    (a : Array α n) (i : Std.Usize) (x : α)
    (h : Array.index_usize a i = .ok x) : i.val < n.val := by
  have hlen : i.val < a.val.length := by
    by_contra hnot
    have hnone : a[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa [a.property] using hlen

private theorem scan_success_length (proof : Slice Std.U8)
    (h : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    proof.val.length = 57607 := by
  have hlen : Slice.len proof = 57607#usize := by
    by_cases hlen : Slice.len proof = 57607#usize
    · exact hlen
    · have hneq : (Slice.len proof != 57607#usize) = true := by simp [hlen]
      have hfalse : MultiproofParserRef.parser_reference.scan proof = .ok false := by
        simp [MultiproofParserRef.parser_reference.scan, hneq]
      rw [hfalse] at h
      cases h
  have hv := congrArg UScalar.val hlen
  simpa [Slice.len, Slice.length] using hv

theorem scanned_query_prefix_success_current_opening
    (base : Ops) (proof : Slice Std.U8)
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
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true)
    (hactual : AspisR1Stage2QueryTailCut.query_values_forward_prefix_ops
      actualOpeningOp (currentFourDotsAsPrefix (install base)) proof p acc g obs geometry pending=.ok out) :
    ∃ (i : Std.U32) (u : Std.Usize) (q : Slice Std.U8)
      (dots : Array Wide 4#usize) (arrayQ : Array Std.U8 608#usize)
      (v0 v1 v2 v3 : Wide),
      Array.index_usize p.queries acc.next=.ok i ∧
      lift (UScalar.cast .Usize i)=.ok u ∧
      actualOpeningOp proof acc.next=.ok q ∧
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
  obtain ⟨i0, u0, q0, dots0, hindex0, _, _, _, _⟩ :=
    query_values_forward_prefix_actual_s4 actualOpeningOp (install base)
      proof p acc g obs geometry pending out hactual
  have hnext : acc.next.val < 22 := by
    have hi := index_success_bound p.queries acc.next i0 hindex0
    simpa using hi
  have hlen : proof.val.length = 57607 := scan_success_length proof hscan
  have hopening : ∀ q, actualOpeningOp proof acc.next=.ok q →
      q.val=proof.val.slice (10055+acc.next.val*832) (10055+acc.next.val*832+832) := by
    intro q hq
    obtain ⟨q', hq', hbytes⟩ :=
      AspisR1S4OpeningBytesFromCurrentV1.opening_slice_exact proof acc.next hnext
        (by omega : 28359 ≤ proof.val.length)
    have heq : q' = q := by
      have := hq'.symm.trans hq
      exact Result.ok.inj this
    simpa [actualOpeningOp] using heq ▸ hbytes
  exact scanned_query_prefix_success_literal_values actualOpeningOp base proof p acc g obs
    geometry pending out gamma claimPowers hgamma hpowers hcaller hlen hnext hopening hscan hactual

#print axioms scanned_query_prefix_success_current_opening
end AspisR1S4ScannedQueryPrefixCurrentOpeningV1

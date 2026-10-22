import S4CanonicalOpeningForwardRootV1
import MultiproofConeStrictScan
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1
namespace AspisR1FastDotsScannedOpeningForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1FastDotsForwardLiteralValueRootV1 (literalOps)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1.MultiproofConeCanonical (bytesOf)
open AspisR1.OraclePortCompactDraft (openingCanonical scan slice)

theorem strict_scan_accepted_opening (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8)
    (hlen : proof.val.length=57607) (hj : j<22)
    (hread : q.val=proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true) :
    openingCanonical (bytesOf q.val) := by
  have hs := AspisR1.MultiproofConeStrictScan.scan_total proof hlen
  rw [hscan] at hs
  have hd : decide (scan (bytesOf proof.val))=true := Result.ok.inj hs.symm
  have hc : scan (bytesOf proof.val) := of_decide_eq_true hd
  have hop := hc.2.2.2 j (List.mem_range.mpr hj)
  have he : bytesOf q.val=slice (bytesOf proof.val) (10055+j*832) 832 := by
    simp [bytesOf,hread,List.slice,slice]
  rw [he]
  exact hop

theorem four_dots_forward_of_scanned_opening
    (base : Ops) (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8)
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (hlen : proof.val.length=57607) (hj : j<22)
    (hread : q.val=proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true)
    (ha : a.val=q.val.slice 0 (608#usize))

    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    :
    ∃ (values : Array Wide 4#usize) (v0 v1 v2 v3 : Wide),
      AspisR1FastDotsCurrent.fast_dots.four_dots (install base) q g=.ok values ∧
      (∀ x∈values.val,AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      values.val=[v0,v1,v2,v3] ∧
      LiteralFieldResult (literalOps base) a g 0#usize v0 ∧ LiteralFieldResult (literalOps base) a g 1#usize v1 ∧
      LiteralFieldResult (literalOps base) a g 2#usize v2 ∧ LiteralFieldResult (literalOps base) a g 3#usize v3 := by
  exact AspisR1FastDotsCanonicalOpeningForwardRootV1.four_dots_forward_of_canonical_opening
    base q a g ha (strict_scan_accepted_opening proof j q hlen hj hread hscan) hcoords

#print axioms strict_scan_accepted_opening
#print axioms four_dots_forward_of_scanned_opening
end AspisR1FastDotsScannedOpeningForwardRootV1

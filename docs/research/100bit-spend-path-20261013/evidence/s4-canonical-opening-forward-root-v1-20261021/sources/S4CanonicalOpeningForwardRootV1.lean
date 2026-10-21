import S4CanonicalSlotInputsRootV1
import S4ForwardLiteralValueRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsCanonicalOpeningForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1FastDotsForwardLiteralValueRootV1 (literalOps)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1.MultiproofConeCanonical (bytesOf)
open AspisR1.OraclePortCompactDraft (canonical openingCanonical)

theorem prefix_length_bound (q : Slice Std.U8) (a : Array Std.U8 608#usize)
    (ha : a.val=q.val.slice 0 (608#usize)) : 608≤q.length := by
  have hl := congrArg List.length ha
  simp [List.slice,a.property] at hl
  change 608≤q.val.length
  omega

theorem opening_payload_canonical (q : Slice Std.U8) (a : Array Std.U8 608#usize)
    (ha : a.val=q.val.slice 0 (608#usize))
    (hc : openingCanonical (bytesOf q.val)) : canonical (bytesOf a.val) := by
  have he : bytesOf a.val=(bytesOf q.val).take 608 := by
    simp [bytesOf,ha,List.slice]
  rw [he]
  exact hc.1

theorem four_dots_forward_of_canonical_opening
    (base : Ops) (q : Slice Std.U8) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (ha : a.val=q.val.slice 0 (608#usize))
    (hc : openingCanonical (bytesOf q.val))
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
  have hq := prefix_length_bound q a ha
  have hpayload := opening_payload_canonical q a ha hc
  exact AspisR1FastDotsForwardLiteralValueRootV1.four_dots_forward_literal_value
    base q a g hq ha hcoords (fun slot hs=>
      AspisR1FastDotsCanonicalSlotInputsRootV1.canonical_slot_input a g slot hs hpayload)

#print axioms prefix_length_bound
#print axioms opening_payload_canonical
#print axioms four_dots_forward_of_canonical_opening
end AspisR1FastDotsCanonicalOpeningForwardRootV1

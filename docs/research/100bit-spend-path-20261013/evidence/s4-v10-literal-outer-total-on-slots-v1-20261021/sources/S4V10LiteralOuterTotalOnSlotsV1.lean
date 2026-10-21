import S4ConcreteReverseClosureRootV1
import S4V10LiteralOuterTransferRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsV10LiteralOuterTotalOnSlotsV1

open AspisR1FastDotsConcreteReverseClosureRootV1
open AspisR1FastDotsConcreteReverseHeadRootV1 (install)
open AspisR1FastDotsV10LiteralOuterTransferRootV1
open AspisR1FastDotsV10CarrierMapV1
open AspisR1FastDotsV10TypedInnerBodyOpsV1 (mapWideArray)
open AspisR1S4FourWrapperCarrierTransportRootV1 (mapArray)

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact

/-- On the retained canonical coordinate/slot domain, the selected literal
V10 four-call body is total and its exact mapped output is the canonical
output of the installed fixed-v6 body. This composes the existing fixed-helper
success theorem with the all-Result literal outer transport; it does not assert
source adoption or Rust Std iterator/from_fn correspondence. -/
theorem literal_outer_total_on_slots
    (base : Ops) (q : Slice Std.U8) (a : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize)
    (hq : 608 ≤ q.length)
    (ha : a.val = q.val.slice 0 (608#usize))
    (hcoords : ∀ j : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        ((mapWideArray g).val[j.val]'(by simpa [mapWideArray] using j.isLt)))
    (hslots : ∀ slot : Usize, slot.val < 4#usize.val →
      AspisR1FastDotsFourCallbacksForwardRootV1.SlotInput a (mapWideArray g) slot) :
    ∃ literalValues : Array V10Wide 4#usize,
      ∃ currentValues : Array Wide 4#usize,
        literalV10Outer (install base) q g = .ok literalValues ∧
        AspisR1FastDotsCurrent.fast_dots.four_dots_fixed (install base) q
          (mapWideArray g) = .ok currentValues ∧
        mapArray wideToEbyK literalValues = currentValues ∧
        (∀ x ∈ currentValues.val,
          AspisR1CurrentWide.Proof.CanonicalWide
            (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) := by
  obtain ⟨currentValues, hfixed, hcanonical⟩ :=
    AspisR1FastDotsConcreteReverseClosureRootV1.fixed_four_total_on_slots
      base q a (mapWideArray g) hq ha hcoords hslots
  have htransport := literal_outer_to_current (install base) q g
  rw [hfixed] at htransport
  cases hliteral : literalV10Outer (install base) q g with
  | ok literalValues =>
      simp only [AspisR1FastDotsV10TailMapRootV1.mapRes, hliteral] at htransport
      have hmapped : mapArray wideToEbyK literalValues = currentValues := Result.ok.inj htransport
      exact ⟨literalValues, currentValues, rfl, hfixed, hmapped, hcanonical⟩
  | fail err => simp [AspisR1FastDotsV10TailMapRootV1.mapRes, hliteral] at htransport
  | div => simp [AspisR1FastDotsV10TailMapRootV1.mapRes, hliteral] at htransport

#print axioms literal_outer_total_on_slots

end AspisR1FastDotsV10LiteralOuterTotalOnSlotsV1

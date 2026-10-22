import S4ForwardFieldMeaningRootV1
import S4LiteralCallbackValueRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsForwardLiteralValueRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (SlotInput install arrayOps)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult callback_field_result_literal)
def literalOps (base : Ops) : Ops := AspisR1FastDotsConcreteTailInstallRootV1.install
  (AspisR1FastDotsAllFourHeadDecodingV1.Outer (arrayOps base))
theorem four_dots_forward_literal_value
    (base : Ops) (q : Slice Std.U8) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (hq : 608≤q.length) (ha : a.val=q.val.slice 0 (608#usize))
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hslots : ∀ slot : Usize, slot.val<4 → SlotInput a g slot) :
    ∃ (values : Array Wide 4#usize) (v0 v1 v2 v3 : Wide),
      AspisR1FastDotsCurrent.fast_dots.four_dots (install base) q g=.ok values ∧
      (∀ x∈values.val,AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      values.val=[v0,v1,v2,v3] ∧
      LiteralFieldResult (literalOps base) a g 0#usize v0 ∧ LiteralFieldResult (literalOps base) a g 1#usize v1 ∧
      LiteralFieldResult (literalOps base) a g 2#usize v2 ∧ LiteralFieldResult (literalOps base) a g 3#usize v3 := by
  obtain ⟨values,v0,v1,v2,v3,hfunction,hcanonical,hvalues,h0,h1,h2,h3⟩ :=
    AspisR1FastDotsForwardFieldMeaningRootV1.four_dots_forward_field_meaning
      base q a g hq ha hcoords hslots
  exact ⟨values,v0,v1,v2,v3,hfunction,hcanonical,hvalues,
    callback_field_result_literal _ _ _ _ _ _ h0,
    callback_field_result_literal _ _ _ _ _ _ h1,
    callback_field_result_literal _ _ _ _ _ _ h2,
    callback_field_result_literal _ _ _ _ _ _ h3⟩

#print axioms four_dots_forward_literal_value
end AspisR1FastDotsForwardLiteralValueRootV1

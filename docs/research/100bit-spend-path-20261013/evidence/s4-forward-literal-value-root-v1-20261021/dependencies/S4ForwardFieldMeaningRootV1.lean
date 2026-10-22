import S4ForwardFieldOpsRootV1
import S4GeneratedFunctionFourCallbacksV2
import S4QueryValuesFourCallbackFieldResultV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsForwardFieldMeaningRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (SlotInput install arrayOps)
open AspisR1FastDotsForwardFieldOpsRootV1 (forward_field_ops_same)
open AspisR1FastDotsQueryValuesFourCallbackFieldResultV2 (CallbackFieldResult callback_field_result_of_trace)
abbrev FieldResult (base : Ops) := CallbackFieldResult (arrayOps base)
  (AspisR1FastDotsConcreteTailInstallRootV1.install
    (AspisR1FastDotsAllFourHeadDecodingV1.Outer (arrayOps base)))

/-- Construct the complete emitted function result and its same-output field
meaning. No successful child callback or parent execution is assumed. The
retained P6 array interpretation and caller parser/canonicality premises remain
explicit, so this is not yet a Rust Std or release-artifact theorem. -/
theorem four_dots_forward_field_meaning
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
      FieldResult base a g 0#usize v0 ∧ FieldResult base a g 1#usize v1 ∧
      FieldResult base a g 2#usize v2 ∧ FieldResult base a g 3#usize v3 := by
  obtain ⟨values,hfunction,hcanonical⟩ :=
    AspisR1FastDotsFunctionForwardRootV1.four_dots_forward base q a g hq ha hcoords hslots
  have hold : AspisR1FastDotsCurrent.fast_dots.four_dots
      (AspisR1FastDotsAllFourHeadDecodingV1.Outer (arrayOps base)) q g=.ok values := by
    rw [forward_field_ops_same]
    exact hfunction
  obtain ⟨arrayQ,hprefix,_harray,v0,v1,v2,v3,hvalues,h0,h1,h2,h3⟩ :=
    AspisR1FastDotsGeneratedFunctionFourCallbacksV2.generated_four_dots_success_four_callback_traces
      (arrayOps base) q g hcoords hold
  have heq : arrayQ=a := Subtype.ext (hprefix.trans ha.symm)
  subst arrayQ
  exact ⟨values,v0,v1,v2,v3,hfunction,hcanonical,hvalues,
    callback_field_result_of_trace _ _ _ _ _ _ h0,
    callback_field_result_of_trace _ _ _ _ _ _ h1,
    callback_field_result_of_trace _ _ _ _ _ _ h2,
    callback_field_result_of_trace _ _ _ _ _ _ h3⟩
#print axioms four_dots_forward_field_meaning
end AspisR1FastDotsForwardFieldMeaningRootV1

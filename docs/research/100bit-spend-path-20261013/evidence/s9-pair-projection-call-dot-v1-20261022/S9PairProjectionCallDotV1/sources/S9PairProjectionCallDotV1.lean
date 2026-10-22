import S9PairProjectionLoopDotV1
import S9PairCallerStepReachedHelperV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9PairProjectionCallDotV1
open AspisR1S9PairCallerStepV1

abbrev U := Std.Usize
abbrev W := Array field.WideExact (7#usize)
abbrev Canonical := AspisR1S9PairProjectionLoopDotV1.Canonical
abbrev decode := AspisR1S9PairProjectionLoopDotV1.decode

/-- A successful S2-specialized projection caller exposes the same helper
result and four-slot projection-loop result. Composing the loop dot theorem
returns the canonical projected cell and its exact same-run dot equation. -/
theorem s2_projection_success_has_dot4
    (w : weights.Weights) (f : Slice U8)
    (ap0 ap1 : AspisR1S9PairOutputReadCanonicalV1.PairW)
    (low : Array field.WideExact (16#usize))
    (parts out : W)
    (hvariant : w.variant = transport.Variant.S2)
    (hprojection : weights.Weights.pair_s2_libra_parts_projection
      w f ap0 ap1 low parts = .ok out)
    (hp0 : ∀ (j : U) (x : AspisR1S9PairOutputReadCanonicalV1.P6W),
      Array.index_usize (AspisR1S9PairOutputReadCanonicalV1.mapArray
        AspisR1S9PairOutputReadCanonicalV1.ToP6W
        (AspisR1S9PairOutputReadCanonicalV1.mapArray
          AspisR1S9PairOutputReadCanonicalV1.PairMapW ap0)) j = .ok x →
      AspisR1S9PairOutputReadCanonicalV1.Canonical x)
    (hap1 : ∀ (j : U) (x : AspisR1S9PairOutputReadCanonicalV1.P6W),
      Array.index_usize (AspisR1S9PairOutputReadCanonicalV1.mapArray
        AspisR1S9PairOutputReadCanonicalV1.ToP6W
        (AspisR1S9PairOutputReadCanonicalV1.mapArray
          AspisR1S9PairOutputReadCanonicalV1.PairMapW ap1)) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hextra : ∀ (j : U) (x : AspisR1S9CandidateHelperV1.field.QM31),
      Array.index_usize (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ w.extra) j = .ok x →
      AspisR1S9CandidateHighArraySemanticsV1.CanonicalP6
        (AspisR1S9CandidateHelperV1.toP6Q x))
    (hinitial : ∀ x, Array.index_usize parts 4#usize = .ok x → Canonical x) :
    ∃ libra old v0 c0 v1 c1 v2 c2 v3 c3 final,
      weights.factored_s2_libra_weights ap0 ap1 w.extra = .ok libra ∧
      Array.index_usize parts 4#usize = .ok old ∧
      weights.field f 0#usize = .ok v0 ∧ Array.index_usize libra 0#usize = .ok c0 ∧
      weights.field f 1#usize = .ok v1 ∧ Array.index_usize libra 1#usize = .ok c1 ∧
      weights.field f 2#usize = .ok v2 ∧ Array.index_usize libra 2#usize = .ok c2 ∧
      weights.field f 3#usize = .ok v3 ∧ Array.index_usize libra 3#usize = .ok c3 ∧
      Array.index_usize out 4#usize = .ok final ∧ Canonical final ∧
      decode final = (((decode old + decode v0 * decode c0) +
        decode v1 * decode c1) + decode v2 * decode c2) + decode v3 * decode c3 := by
  obtain ⟨libra, hhelper, hloop⟩ :=
    AspisR1S9PairCallerStepReachedHelperV1.s2_projection_success_reaches_helper_and_loop
      w f ap0 ap1 low parts out hvariant hprojection
  obtain ⟨old, v0, c0, v1, c1, v2, c2, v3, c3,
      hold, hfield0, hcoef0, hfield1, hcoef1, hfield2, hcoef2, hfield3, hcoef3,
      final, hfinal, hfinalCan, hdecode⟩ :=
    AspisR1S9PairProjectionLoopDotV1.projection_loop_success_dot4
      ap0 ap1 w.extra libra f parts out hhelper hp0 hap1 hextra hinitial hloop
  exact ⟨libra, old, v0, c0, v1, c1, v2, c2, v3, c3, final,
    hhelper, hold, hfield0, hcoef0, hfield1, hcoef1, hfield2, hcoef2,
    hfield3, hcoef3, hfinal, hfinalCan, hdecode⟩

#print axioms s2_projection_success_has_dot4
end AspisR1S9PairProjectionCallDotV1

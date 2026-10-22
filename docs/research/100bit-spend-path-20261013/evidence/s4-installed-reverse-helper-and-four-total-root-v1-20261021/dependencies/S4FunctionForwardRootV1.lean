import S4FourCallbacksForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsFunctionForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (SlotInput install OuterFn)

theorem prefix608_forward (q : Slice Std.U8) (a : Array Std.U8 608#usize)
    (hq : 608≤q.length) (ha : a.val=q.val.slice 0 (608#usize)) :
    ∃ s : Slice Std.U8,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
        q {«end»:=608#usize}=.ok s ∧
      core.array.TryFromSharedArraySlice.try_from 608#usize s=.ok (.Ok a) := by
  obtain ⟨s,hs,hbytes,hlen⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec {«end»:=608#usize} q (by simpa using hq))
  have hlenU : s.len=608#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val,hlen]
  have hlenNat : s.val.length=(608#usize).val := hlen
  let copied : Array Std.U8 608#usize := ⟨s.val,hlenNat⟩
  have heq : copied=a := by
    apply Subtype.ext
    exact hbytes.trans ha.symm
  have hcopy : core.array.TryFromSharedArraySlice.try_from 608#usize s=.ok (.Ok copied) := by
    simp only [core.array.TryFromSharedArraySlice.try_from,dif_pos hlenU]
    rfl
  refine ⟨s,?_,?_⟩
  · exact hs
  · rw [heq] at hcopy
    exact hcopy

theorem four_dots_forward
    (base : Ops) (q : Slice Std.U8) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (hq : 608≤q.length) (ha : a.val=q.val.slice 0 (608#usize))
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hslots : ∀ slot : Usize, slot.val<4 → SlotInput a g slot) :
    ∃ values : Array Wide 4#usize,
      AspisR1FastDotsCurrent.fast_dots.four_dots (install base) q g=.ok values ∧
      (∀ x∈values.val,AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) := by
  obtain ⟨s,hs,hcopy⟩ := prefix608_forward q a hq ha
  obtain ⟨values,harray,hcan⟩ := AspisR1FastDotsFourCallbacksForwardRootV1.four_callbacks_forward
    base a g hcoords hslots
  refine ⟨values,?_,hcan⟩
  simp [AspisR1FastDotsCurrent.fast_dots.four_dots,hs,hcopy,
    core.result.Result.unwrap,harray]

#print axioms prefix608_forward
#print axioms four_dots_forward
end AspisR1FastDotsFunctionForwardRootV1

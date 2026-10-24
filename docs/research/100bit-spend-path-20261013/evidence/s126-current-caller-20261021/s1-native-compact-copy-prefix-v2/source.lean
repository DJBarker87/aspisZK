import S1NativeCompactEntryLengthV1
set_option autoImplicit false
namespace AspisS1NativeCompactCopyPrefix
open Aeneas Aeneas.Std Result
open AspisS1NativeCompactBodyFrame

/-- Exact actual source range-copy extension of an already copied prefix.
The mutable range, source range and copy successes are those reached by the
caller; no supplied byte equality or idealized write replaces them. -/
theorem range_copy (input out window source replacement : Slice U8)
    (back : Slice U8 → Slice U8) (start stop : Usize)
    (hmut : core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice U8) out
      {start:=start,«end»:=stop}=ok (window,back))
    (hsource : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) input
      {start:=start,«end»:=stop}=ok source)
    (hcopy : core.slice.Slice.copy_from_slice core.marker.CopyU8 window source=ok replacement)
    (earlier : Prefix start.val input out) : Prefix stop.val input (back replacement) := by
  have outBounds : start≤stop ∧ stop.val≤out.length := by
    simp only [Slice.index_mut_SliceIndexRangeUsizeSliceInst] at hmut
    unfold core.slice.index.SliceIndexRangeUsizeSlice.index_mut at hmut
    split at hmut
    · assumption
    · cases hmut
  have inputBounds : start≤stop ∧ stop.val≤ input.length := by
    simp only [Slice.index_SliceIndexRangeUsizeSliceInst] at hsource
    unfold core.slice.index.SliceIndexRangeUsizeSlice.index at hsource
    split at hsource
    · assumption
    · cases hsource
  obtain ⟨pair,call,facts⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec
      {start:=start,«end»:=stop} out outBounds.1 outBounds.2)
  have same : pair=(window,back) := Result.ok.inj (call.symm.trans hmut)
  subst pair
  obtain ⟨sourceValue,sourceCall,sourceFacts⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      {start:=start,«end»:=stop} input inputBounds.1 inputBounds.2)
  have sameSource : sourceValue=source := Result.ok.inj (sourceCall.symm.trans hsource)
  subst sourceValue
  have copied : replacement=source := by
    unfold core.slice.Slice.copy_from_slice at hcopy
    split at hcopy
    · exact (Result.ok.inj hcopy).symm
    · cases hcopy
  subst replacement
  have outEnd : stop.val≤out.val.length := outBounds.2
  have inputEnd : stop.val≤ input.val.length := inputBounds.2
  intro j hj
  by_cases before : j<start.val
  · exact (AspisS1NativeCompactFrame.range_prefix out window back start stop hmut source j before).trans
      (earlier j before)
  · have updated := congrArg (fun s : Slice U8 => s.val) (facts.2.2 source)
    change (back source).val=out.val.setSlice! start.val source.val at updated
    rw [updated]
    have sourceLength : source.val.length=stop.val-start.val := sourceFacts.2
    have middle := List.setSlice!_getElem?_middle out.val source.val start.val j
      (by omega)
    rw [middle]
    rw [sourceFacts.1]
    have byte := List.getElem?_slice start.val stop.val (j-start.val) input.val
      (by omega)
    simpa only [Nat.add_sub_of_le (Nat.le_of_not_gt before)] using byte

#print axioms range_copy
end AspisS1NativeCompactCopyPrefix

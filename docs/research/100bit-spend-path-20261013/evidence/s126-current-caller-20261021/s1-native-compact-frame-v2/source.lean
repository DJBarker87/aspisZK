import S1LoopSafetyV1
set_option autoImplicit false
namespace AspisS1NativeCompactFrame
open Aeneas Aeneas.Std Result

/-- The actual Std mutable-range return lens preserves every earlier byte,
for every returned replacement buffer. No expansion-leaf correctness or
replacement-length premise is needed for this prefix-only property. -/
theorem range_prefix {T : Type} (input window : Slice T)
    (back : Slice T → Slice T) (start stop : Usize)
    (success : core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice T) input
      {start:=start,«end»:=stop}=ok (window,back)) :
    ∀ replacement (j : Nat), j<start.val →
      (back replacement).val[j]?=input.val[j]? := by
  simp only [Slice.index_mut_SliceIndexRangeUsizeSliceInst] at success
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index_mut at success
  split at success
  · have same := Result.ok.inj success
    have lens := congrArg Prod.snd same
    intro replacement j before
    have sameBytes := congrArg (fun f : Slice T → Slice T => (f replacement).val[j]?) lens
    change (input.val.setSlice! start.val replacement.val)[j]? = (back replacement).val[j]? at sameBytes
    exact sameBytes.symm.trans (List.setSlice!_getElem?_prefix input.val replacement.val start.val j before)
  · cases success

#print axioms range_prefix
end AspisS1NativeCompactFrame

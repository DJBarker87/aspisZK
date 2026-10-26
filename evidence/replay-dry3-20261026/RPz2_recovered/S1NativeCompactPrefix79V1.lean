import S1NativeCompactThreeRowsV1
set_option autoImplicit false
namespace AspisS1NativeCompactPrefix79
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1NativeCompactBodyFrame AspisS1NativeCompactCopyPrefix

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (m >>= k)=ok v) : ∃ x,m=ok x ∧ k x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => cases h
  | div => cases h
private theorem pair_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b)=ok v) :
    ∃ a b,m=ok (a,b) ∧ k a b=ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => cases h
  | div => cases h

private theorem rangeTo_copy (input out header source replacement : Slice U8)
    (back : Slice U8 → Slice U8) (stop : Usize)
    (hmut : core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice U8) out {«end»:=stop}=ok (header,back))
    (hsource : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeToUsizeSlice U8) input {«end»:=stop}=ok source)
    (hcopy : core.slice.Slice.copy_from_slice core.marker.CopyU8 header source=ok replacement) :
    Prefix stop.val input (back replacement) := by
  have zeroVal : (0#usize : Usize).val=0 := by scalar_tac
  have zero : (0#usize : Usize)≤stop := by scalar_tac
  have mutRange : core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice U8) out
      {start:=0#usize,«end»:=stop}=ok (header,back) := by
    simp only [Slice.index_mut_SliceIndexRangeUsizeSliceInst]
    simp only [Slice.index_mut_SliceIndexRangeToUsizeSliceInst] at hmut
    unfold core.slice.index.SliceIndexRangeUsizeSlice.index_mut
    unfold core.slice.index.SliceIndexRangeToUsizeSlice.index_mut at hmut
    simpa only [zero,zeroVal,true_and] using hmut
  have sourceRange : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) input
      {start:=0#usize,«end»:=stop}=ok source := by
    simp only [Slice.index_SliceIndexRangeUsizeSliceInst]
    simp only [Slice.index_SliceIndexRangeToUsizeSliceInst] at hsource
    unfold core.slice.index.SliceIndexRangeUsizeSlice.index
    unfold core.slice.index.SliceIndexRangeToUsizeSlice.index at hsource
    simpa only [zero,zeroVal,true_and] using hsource
  exact range_copy input out header source replacement back 0#usize stop
    mutRange sourceRange hcopy (fun j hj => by scalar_tac)

/-- On the SAME complete native semantic-expansion return, all bytes through
79 are the actual compact input bytes. This covers both roots, all three
initial row headers, and every remaining loop iteration. The compact value
leaf remains arbitrary; no independent loop/row/copy success is assumed. -/
theorem semantic_prefix79 (ops : Ops) (input out expanded : Slice U8)
    (success : compact.expand_semantic ops input out=ok (.Ok (),expanded)) :
    Prefix 79 input expanded := by
  unfold compact.expand_semantic at success
  obtain ⟨compactLength,hcompactLength,success⟩ := bind_success _ _ _ success
  split at success
  · cases success
  · obtain ⟨logicalLength,hlogicalLength,success⟩ := bind_success _ _ _ success
    split at success
    · cases success
    · obtain ⟨header,back,hheader,success⟩ := pair_success _ _ _ success
      obtain ⟨sourceHeader,hsourceHeader,success⟩ := bind_success _ _ _ success
      obtain ⟨replacement,hreplacement,success⟩ := bind_success _ _ _ success
      have initial := rangeTo_copy input out header sourceHeader replacement back 32#usize
        hheader hsourceHeader hreplacement
      exact AspisS1NativeCompactThreeRows.three_rows ops input (back replacement)
        (.Ok (),expanded) initial success

#print axioms semantic_prefix79
end AspisS1NativeCompactPrefix79

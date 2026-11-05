import S1NativeCompactLoopFrameV1
set_option autoImplicit false
namespace AspisS1NativeCompactBodyFrame
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact

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

private theorem head_copy (input out header sourceHeader replacement : Slice U8)
    (back : Slice U8 → Slice U8) (n : Usize)
    (hheader : core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice U8) out {«end»:=n}=ok (header,back))
    (hsource : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeToUsizeSlice U8) input {«end»:=n}=ok sourceHeader)
    (hcopy : core.slice.Slice.copy_from_slice core.marker.CopyU8 header sourceHeader=ok replacement) :
    Prefix n.val input (back replacement) := by
  simp only [Slice.index_mut_SliceIndexRangeToUsizeSliceInst] at hheader
  simp only [Slice.index_SliceIndexRangeToUsizeSliceInst] at hsource
  unfold core.slice.index.SliceIndexRangeToUsizeSlice.index_mut at hheader
  split at hheader
  · rename_i hout
    have same := Result.ok.inj hheader
    have lens := congrArg Prod.snd same
    unfold core.slice.index.SliceIndexRangeToUsizeSlice.index at hsource
    split at hsource
    · rename_i hin
      have sourceEq := Result.ok.inj hsource
      unfold core.slice.Slice.copy_from_slice at hcopy
      split at hcopy
      · have copied : sourceHeader=replacement := Result.ok.inj hcopy
        subst replacement
        intro j hj
        have lensByte := congrArg (fun f : Slice U8 → Slice U8 => (f sourceHeader).val[j]?) lens
        change (out.val.setSlice! 0 sourceHeader.val)[j]?=(back sourceHeader).val[j]? at lensByte
        have sourceLength : sourceHeader.length=n.val := by
          rw [←sourceEq]
          simp only [Slice.length,List.slice_length]
          scalar_tac
        have middle := List.setSlice!_getElem?_middle out.val sourceHeader.val 0 j
          (by simp only [Nat.zero_le, Nat.sub_zero, true_and]; constructor <;> scalar_tac)
        have sourceByte : sourceHeader.val[j]?=input.val[j]? := by
          rw [←sourceEq]
          simp_lists
        exact lensByte.symm.trans (middle.trans sourceByte)
      · cases hcopy
    · cases hsource
  · cases hheader

/-- The SAME complete native compact semantic expansion preserves the actual
first 32 input bytes, including all loop iterations and codec-error exits
reached after its initial copy. No independent expansion-success or opaque
leaf output equality is assumed. This is accepted-only, not totality. -/
theorem semantic_root_prefix (ops : Ops) (input out expanded : Slice U8)
    (success : compact.expand_semantic ops input out=ok (.Ok (),expanded)) :
    Prefix 32 input expanded := by
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
      have initial := head_copy input out header sourceHeader replacement back 32#usize
        hheader hsourceHeader hreplacement
      have kept := loop_frame ops input (back replacement)
        {start:=0#u8,«end»:=compact.SEMANTIC_ROWS} 32#usize 32#usize 32
        (by scalar_tac) (.Ok (),expanded) success
      exact fun j hj => (kept j hj).trans (initial j hj)

#print axioms semantic_root_prefix
end AspisS1NativeCompactBodyFrame

import S1NativeCompactRootV1
set_option autoImplicit false
namespace AspisS1NativeCompactLengths
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1NativeCompactBodyFrame

def LengthFrame (before : Slice U8) : ControlFlow State Exit → Prop
  | .cont (_,after,_,_) => after.length=before.length
  | .done (_,after) => after.length=before.length

/-- Length of the actual returned mutable range lens, for any replacement. -/
theorem range_length {T : Type} (input window : Slice T)
    (back : Slice T → Slice T) (start stop : Usize)
    (success : core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice T) input
      {start:=start,«end»:=stop}=ok (window,back)) (replacement : Slice T) :
    (back replacement).length=input.length := by
  simp only [Slice.index_mut_SliceIndexRangeUsizeSliceInst] at success
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index_mut at success
  split at success
  · have same := Result.ok.inj success
    have lens := congrArg Prod.snd same
    have sameLength := congrArg (fun f : Slice T → Slice T => (f replacement).length) lens
    change (input.val.setSlice! start.val replacement.val).length=(back replacement).length at sameLength
    exact sameLength.symm.trans (List.length_setSlice! input.val start.val replacement.val)
  · cases success

theorem rangeTo_length {T : Type} (input window : Slice T)
    (back : Slice T → Slice T) (stop : Usize)
    (success : core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice T) input
      {«end»:=stop}=ok (window,back)) (replacement : Slice T) :
    (back replacement).length=input.length := by
  simp only [Slice.index_mut_SliceIndexRangeToUsizeSliceInst] at success
  unfold core.slice.index.SliceIndexRangeToUsizeSlice.index_mut at success
  split at success
  · have same := Result.ok.inj success
    have lens := congrArg Prod.snd same
    have sameLength := congrArg (fun f : Slice T → Slice T => (f replacement).length) lens
    change (input.val.setSlice! 0 replacement.val).length=(back replacement).length at sameLength
    exact sameLength.symm.trans (List.length_setSlice! input.val 0 replacement.val)
  · cases success

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
/-- One unchanged native source step preserves buffer length on every
accepted continuation or exit, independently of the value-expansion leaf. -/
theorem body_length (ops : Ops) (input out : Slice U8)
    (iter : core.ops.range.Range U8) (src dst : Usize) (r : ControlFlow State Exit)
    (call : compact.expand_semantic_loop.body ops input iter out src dst=ok r) :
    LengthFrame out r := by
  unfold compact.expand_semantic_loop.body at call
  obtain ⟨next,iter1,hnext,call⟩ := pair_success _ _ _ call
  cases next with
  | none =>
    change (if src != Slice.len input then
      ok (.done (.Err AspisR1CurrentCaller.compact.CodecError.Length,out))
      else if dst != Slice.len out then
        ok (.done (.Err AspisR1CurrentCaller.compact.CodecError.Length,out))
      else ok (.done (.Ok (),out)))=ok r at call
    split at call
    · have same := Result.ok.inj call
      subst r
      rfl
    · split at call
      · have same := Result.ok.inj call
        subst r
        rfl
      · have same := Result.ok.inj call
        subst r
        rfl
  | some row =>
    obtain ⟨shape,hshape,call⟩ := bind_success _ _ _ call
    cases shape with
    | none =>
      change ok (.done (.Err AspisR1CurrentCaller.compact.CodecError.Length,out))=ok r at call
      have same := Result.ok.inj call
      subst r
      rfl
    | some shape =>
      rcases shape with ⟨tag,size⟩
      simp (config := {zeta := true}) only [core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at call
      obtain ⟨headerEnd,hheaderEnd,call⟩ := bind_success _ _ _ call
      obtain ⟨header,back,hheader,call⟩ := pair_success _ _ _ call
      obtain ⟨sourceHeaderEnd,hsourceHeaderEnd,call⟩ := bind_success _ _ _ call
      obtain ⟨sourceHeader,hsourceHeader,call⟩ := bind_success _ _ _ call
      obtain ⟨newHeader,hnewHeader,call⟩ := bind_success _ _ _ call
      obtain ⟨isCompact,hisCompact,call⟩ := bind_success _ _ _ call
      have headerLength := range_length out header back dst headerEnd hheader newHeader
      cases isCompact with
      | false =>
        obtain ⟨payloadEnd,hpayloadEnd,call⟩ := bind_success _ _ _ call
        obtain ⟨payload,backPayload,hpayload,call⟩ := pair_success _ _ _ call
        obtain ⟨sourceEnd,hsourceEnd,call⟩ := bind_success _ _ _ call
        obtain ⟨sourcePayload,hsourcePayload,call⟩ := bind_success _ _ _ call
        obtain ⟨replacement,hreplacement,call⟩ := bind_success _ _ _ call
        have same := Result.ok.inj call
        subst r
        exact (range_length _ payload backPayload headerEnd payloadEnd hpayload replacement).trans headerLength
      | true =>
        obtain ⟨half,hhalf,call⟩ := bind_success _ _ _ call
        obtain ⟨sourceEnd,hsourceEnd,call⟩ := bind_success _ _ _ call
        obtain ⟨sourcePayload,hsourcePayload,call⟩ := bind_success _ _ _ call
        obtain ⟨payloadEnd,hpayloadEnd,call⟩ := bind_success _ _ _ call
        obtain ⟨payload,backPayload,hpayload,call⟩ := pair_success _ _ _ call
        obtain ⟨expanded,replacement,hexpanded,call⟩ := pair_success _ _ _ call
        have payloadLength := (range_length _ payload backPayload headerEnd payloadEnd hpayload replacement).trans headerLength
        cases expanded with
        | Err error =>
          change ok (.done (.Err error,backPayload replacement))=ok r at call
          have same := Result.ok.inj call
          subst r
          exact payloadLength
        | Ok value =>
          change (do let sourceNext ← sourceHeaderEnd + half
                     ok (.cont (iter1,backPayload replacement,sourceNext,payloadEnd)))=ok r at call
          obtain ⟨sourceEnd1,hsourceEnd1,call⟩ := bind_success _ _ _ call
          have same := Result.ok.inj call
          subst r
          exact payloadLength

#print axioms range_length
#print axioms rangeTo_length
#print axioms body_length
end AspisS1NativeCompactLengths

import S1NativeCompactFrameV1
set_option autoImplicit false
namespace AspisS1NativeCompactBodyFrame
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact
abbrev State := core.ops.range.Range U8 × Slice U8 × Usize × Usize
abbrev Exit := core.result.Result Unit compact.CodecError × Slice U8

def Prefix (n : Nat) (before after : Slice U8) : Prop :=
  ∀ j, j<n → after.val[j]?=before.val[j]?
def Frame (n : Nat) (before : Slice U8) : ControlFlow State Exit → Prop
  | .cont (_,after,_,dst) => n≤dst.val ∧ Prefix n before after
  | .done (_,after) => Prefix n before after

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
private theorem add_value (a b c : Usize) (h : a+b=ok c) : c.val=a.val+b.val := by
  have facts := UScalar.add_equiv a b
  rw [h] at facts
  exact facts.2.1

/-- One actual emitted native semantic-expansion step preserves its earlier
bytes, on both ordinary and error exits and for every value-expansion leaf.
The open leaf is confined by the source's actual returned slice lens. -/
theorem body_frame (ops : Ops) (input out : Slice U8)
    (iter : core.ops.range.Range U8) (src dst : Usize) (n : Nat)
    (before : n≤dst.val) (r : ControlFlow State Exit)
    (call : compact.expand_semantic_loop.body ops input iter out src dst=ok r) :
    Frame n out r := by
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
      exact fun _ _ => rfl
    · split at call
      · have same := Result.ok.inj call
        subst r
        exact fun _ _ => rfl
      · have same := Result.ok.inj call
        subst r
        exact fun _ _ => rfl
  | some row =>
    obtain ⟨shape,hshape,call⟩ := bind_success _ _ _ call
    cases shape with
    | none =>
      change ok (.done (.Err AspisR1CurrentCaller.compact.CodecError.Length,out))=ok r at call
      have same := Result.ok.inj call
      subst r
      exact fun _ _ => rfl
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
      have headerPrefix : Prefix n out (back newHeader) := by
        intro j hj
        exact AspisS1NativeCompactFrame.range_prefix out header back dst headerEnd hheader
          newHeader j (by omega)
      have nextBound : n≤headerEnd.val := by
        have := add_value dst 5#usize headerEnd hheaderEnd
        omega
      cases isCompact with
      | false =>
        obtain ⟨payloadEnd,hpayloadEnd,call⟩ := bind_success _ _ _ call
        obtain ⟨payload,backPayload,hpayload,call⟩ := pair_success _ _ _ call
        obtain ⟨sourceEnd,hsourceEnd,call⟩ := bind_success _ _ _ call
        obtain ⟨sourcePayload,hsourcePayload,call⟩ := bind_success _ _ _ call
        obtain ⟨replacement,hreplacement,call⟩ := bind_success _ _ _ call
        have same := Result.ok.inj call
        subst r
        refine ⟨?_,?_⟩
        · have := add_value headerEnd size payloadEnd hpayloadEnd
          omega
        · intro j hj
          exact (AspisS1NativeCompactFrame.range_prefix _ payload backPayload headerEnd payloadEnd
            hpayload replacement j (by omega)).trans (headerPrefix j hj)
      | true =>
        obtain ⟨half,hhalf,call⟩ := bind_success _ _ _ call
        obtain ⟨sourceEnd,hsourceEnd,call⟩ := bind_success _ _ _ call
        obtain ⟨sourcePayload,hsourcePayload,call⟩ := bind_success _ _ _ call
        obtain ⟨payloadEnd,hpayloadEnd,call⟩ := bind_success _ _ _ call
        obtain ⟨payload,backPayload,hpayload,call⟩ := pair_success _ _ _ call
        obtain ⟨expanded,replacement,hexpanded,call⟩ := pair_success _ _ _ call
        have payloadPrefix : Prefix n out (backPayload replacement) := by
          intro j hj
          exact (AspisS1NativeCompactFrame.range_prefix _ payload backPayload headerEnd payloadEnd
            hpayload replacement j (by omega)).trans (headerPrefix j hj)
        cases expanded with
        | Err error =>
          change ok (.done (.Err error,backPayload replacement))=ok r at call
          have same := Result.ok.inj call
          subst r
          exact payloadPrefix
        | Ok value =>
          change (do let sourceNext ← sourceHeaderEnd + half
                     ok (.cont (iter1,backPayload replacement,sourceNext,payloadEnd)))=ok r at call
          obtain ⟨sourceEnd1,hsourceEnd1,call⟩ := bind_success _ _ _ call
          have same := Result.ok.inj call
          subst r
          refine ⟨?_,payloadPrefix⟩
          have := add_value headerEnd size payloadEnd hpayloadEnd
          omega

#print axioms body_frame
end AspisS1NativeCompactBodyFrame

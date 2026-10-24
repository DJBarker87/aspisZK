import S1NativeCompactCopyPrefixV1
set_option autoImplicit false
namespace AspisS1NativeCompactOrdinaryPrefix
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

/-- Exact native ordinary-row step extends the copied prefix through both
header and payload. Iterator/shape/checked-add facts are instantiated at the
three fixed source rows by the enclosing entry theorem. -/
theorem ordinary_prefix (ops : Ops) (input out : Slice U8)
    (iter iter1 : core.ops.range.Range U8) (row tag : U8)
    (size position headerEnd next : Usize)
    (advance : core.iter.range.IteratorRange.next core.iter.range.StepU8 iter=ok (some row,iter1))
    (shape : r1_wire.row_shape row=ok (some (tag,size)))
    (ordinary : compact.compact_row row=ok false)
    (addHeader : position+5#usize=ok headerEnd) (addPayload : headerEnd+size=ok next)
    (earlier : Prefix position.val input out) (r : ControlFlow State Exit)
    (call : compact.expand_semantic_loop.body ops input iter out position position=ok r) :
    ∃ updated, r=.cont (iter1,updated,next,next) ∧ Prefix next.val input updated := by
  unfold compact.expand_semantic_loop.body at call
  obtain ⟨o,it,hit,call⟩ := pair_success _ _ _ call
  have pairEq := Result.ok.inj (hit.symm.trans advance)
  have oEq : o=some row := congrArg Prod.fst pairEq
  have itEq : it=iter1 := congrArg Prod.snd pairEq
  subst o
  subst it
  obtain ⟨actualShape,hshape,call⟩ := bind_success _ _ _ call
  have shapeEq : actualShape=some (tag,size) := Result.ok.inj (hshape.symm.trans shape)
  subst actualShape
  simp (config := {zeta := true}) only [core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at call
  obtain ⟨headerStop,hheaderStop,call⟩ := bind_success _ _ _ call
  have stopEq := Result.ok.inj (hheaderStop.symm.trans addHeader)
  subst headerStop
  obtain ⟨header,back,hheader,call⟩ := pair_success _ _ _ call
  obtain ⟨sourceStop,hsourceStop,call⟩ := bind_success _ _ _ call
  have sourceStopEq := Result.ok.inj (hsourceStop.symm.trans addHeader)
  subst sourceStop
  obtain ⟨sourceHeader,hsourceHeader,call⟩ := bind_success _ _ _ call
  obtain ⟨replacementHeader,hcopyHeader,call⟩ := bind_success _ _ _ call
  obtain ⟨compactRow,hcompactRow,call⟩ := bind_success _ _ _ call
  have compactEq := Result.ok.inj (hcompactRow.symm.trans ordinary)
  subst compactRow
  obtain ⟨payloadStop,hpayloadStop,call⟩ := bind_success _ _ _ call
  have payloadStopEq := Result.ok.inj (hpayloadStop.symm.trans addPayload)
  subst payloadStop
  obtain ⟨payload,backPayload,hpayload,call⟩ := pair_success _ _ _ call
  obtain ⟨sourceEnd,hsourceEnd,call⟩ := bind_success _ _ _ call
  have sourceEndEq := Result.ok.inj (hsourceEnd.symm.trans addPayload)
  subst sourceEnd
  obtain ⟨replacement,hcopyPayloadSource,call⟩ := bind_success _ _ _ call
  obtain ⟨replacementPayload,hcopyPayload,call⟩ := bind_success _ _ _ call
  have headerKept := range_copy input out header sourceHeader replacementHeader back
    position headerEnd hheader hsourceHeader hcopyHeader earlier
  have payloadKept := range_copy input (back replacementHeader) payload replacement replacementPayload
    backPayload headerEnd next hpayload hcopyPayloadSource hcopyPayload headerKept
  exact ⟨backPayload replacementPayload,(Result.ok.inj call).symm,payloadKept⟩

#print axioms ordinary_prefix
end AspisS1NativeCompactOrdinaryPrefix

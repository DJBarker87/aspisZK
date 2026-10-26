import S1NativePreparePhysicalRootV1
set_option autoImplicit false
namespace AspisS1ParsedSecondRootBytes
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedPrefixTrace

private theorem first_three {bytes : Slice U8} {rows : List U8} {frames : List (Slice U8)}
    {start finish : Usize}
    (chain : RecordChain bytes (0#u8::1#u8::2#u8::rows) start frames finish) :
    ∃ f0 f1 f2 rest n0 n1 n2,
      frames=f0::f1::f2::rest ∧
      AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes 0#u8 start=ok (.Ok (f0,n0)) ∧
      AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes 1#u8 n0=ok (.Ok (f1,n1)) ∧
      AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes 2#u8 n1=ok (.Ok (f2,n2)) := by
  cases chain with
  | cons h0 tail0 =>
    cases tail0 with
    | cons h1 tail1 =>
      cases tail1 with
      | cons h2 tail2 => exact ⟨_,_,_,_,_,_,_,rfl,h0,h1,h2⟩

private theorem empty_step (bytes framed : Slice U8) (row : U8) (start next : Usize)
    (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (0#u8,0#usize)))
    (call : AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes row start=ok (.Ok (framed,next))) :
    next.val=start.val+5 := by
  obtain ⟨tag,size,payload,hshape,hnext,hlen,hbytes,hparsed⟩ :=
    AspisR1.ExtractedPrefixRecordStep.parse_record_at_success bytes framed row start next call
  have pair := Option.some.inj (Result.ok.inj (hshape.symm.trans shape))
  have sizeEq : size=0#usize := congrArg Prod.snd pair
  subst size
  scalar_tac

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (m >>= k)=ok v) : ∃ x,m=ok x ∧ k x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => cases h
  | div => cases h

/-- Actual complete Prefix parsing and the reached source row-2 payload call
identify its bytes at logical offsets 47..79. No chosen frame, offset,
parse_record call or payload identity is supplied independently. -/
theorem row2_bytes (bytes : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (payload : Slice U8)
    (parsed : AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (read : AspisR1PublicPreparation.FinishModel.payload pre 2#u8=ok (.Ok payload)) :
    payload.val=bytes.val.slice 47 79 := by
  have source := AspisR1PublicPreparation.PrefixAdapter.parse_success bytes pre parsed
  obtain ⟨finish,chain,allBytes⟩ :=
    (AspisR1.ExtractedPrefixParse.parse_success bytes
      (AspisR1PublicPreparation.PrefixAdapter.toOld pre) source).2
  obtain ⟨f0,f1,f2,rest,n0,n1,n2,frames,h0,h1,h2⟩ := first_three chain
  change pre.records.val=f0::f1::f2::rest at frames
  have next0 := empty_step bytes f0 0#u8 32#usize n0 rfl h0
  have n0Eq : n0=37#usize := by apply UScalar.eq_of_val_eq;scalar_tac
  subst n0
  have next1 := empty_step bytes f1 1#u8 37#usize n1 rfl h1
  have n1Eq : n1=42#usize := by apply UScalar.eq_of_val_eq;scalar_tac
  subst n1
  obtain ⟨tag,size,value,hshape,hnext,hlen,hframe,hparsed⟩ :=
    AspisR1.ExtractedPrefixRecordStep.parse_record_at_success bytes f2 2#u8 42#usize n2 h2
  have shape : AspisR1PrefixAggregateParser.r1_wire.row_shape 2#u8=ok (some (1#u8,32#usize)) := rfl
  have pair := Option.some.inj (Result.ok.inj (hshape.symm.trans shape))
  have sizeEq : size=32#usize := congrArg Prod.snd pair
  subst size
  have frameBytes : f2.val=(bytes.val.drop 42).take 37 := by
    simpa only [show (42#usize : Usize).val=42 by scalar_tac,
      show (32#usize : Usize).val=32 by scalar_tac] using hframe
  have index : Array.index_usize pre.records 2#usize=ok f2 := by
    unfold Array.index_usize
    have cell : pre.records[2#usize]?=some f2 := by
      change pre.records.val[(2#usize : Usize).val]?=some f2
      rw [show (2#usize : Usize).val=2 by scalar_tac,frames]
      rfl
    rw [cell]
  have record : AspisR1PublicPreparation.r1_wire.Prefix.record pre 2#u8=ok (.Ok f2) := by
    unfold AspisR1PublicPreparation.r1_wire.Prefix.record
    have small : ¬ (2#u8 : U8)≥27#u8 := by scalar_tac
    have cast : UScalar.cast .Usize (2#u8)=2#usize := by apply UScalar.eq_of_val_eq;scalar_tac
    simp only [if_neg small,cast,lift,bind_tc_ok,index]
  unfold AspisR1PublicPreparation.FinishModel.payload at read
  rw [record] at read
  change (do
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) f2 {start:=5#usize}
    ok (core.result.Result.Ok s))=ok (.Ok payload) at read
  obtain ⟨actual,hactual,returned⟩ := bind_success _ _ _ read
  have same : actual=payload := core.result.Result.Ok.inj (Result.ok.inj returned)
  subst actual
  simp only [Slice.index_SliceIndexRangeFromUsizeSliceInst] at hactual
  unfold core.slice.index.SliceIndexRangeFromUsizeSlice.index at hactual
  split at hactual
  · have sameBytes := congrArg (fun s : Slice U8 => s.val) (Result.ok.inj hactual)
    have payloadBytes : payload.val=f2.val.drop 5 := by
      simpa only [Slice.drop,show (5#usize : Usize).val=5 by scalar_tac] using sameBytes.symm
    rw [payloadBytes,frameBytes]
    simpa only [List.slice,List.drop_drop] using
      (List.take_drop (i:=32) (j:=5) (l:=bytes.val.drop 42)).symm
  · cases hactual

#print axioms row2_bytes
end AspisS1ParsedSecondRootBytes

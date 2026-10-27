import RPz7_PSem_TypedPrefix
set_option autoImplicit false
namespace AspisR1.PSem_RecordChain
open Aeneas Aeneas.Std Result ExtractedPrefixTrace

theorem chain_bounds {bytes : Slice U8} {rows : List U8} {offset finish : Usize}
    {frames : List (Slice U8)} (h : RecordChain bytes rows offset frames finish) :
    offset.val ≤ finish.val := by
  induction h with
  | nil => exact Nat.le_refl _
  | @cons row rows offset framed next frames finish step tail ih =>
    obtain ⟨_,size,_,_,nextValue,_,_,_⟩ :=
      ExtractedPrefixRecordStep.parse_record_at_success bytes framed row offset next step
    omega

theorem chain_bytes {bytes : Slice U8} {rows : List U8} {offset finish : Usize}
    {frames : List (Slice U8)} (h : RecordChain bytes rows offset frames finish) :
    (frames.map (fun s => s.val)).flatten =
      (bytes.val.drop offset.val).take (finish.val-offset.val) := by
  induction h with
  | nil => simp
  | @cons row rows offset framed next frames finish step tail ih =>
    obtain ⟨_,size,_,_,nextValue,nextBound,frameValue,_⟩ :=
      ExtractedPrefixRecordStep.parse_record_at_success bytes framed row offset next step
    have later := chain_bounds tail
    simp only [List.map_cons,List.flatten_cons,frameValue,ih]
    have first : 5+size.val=next.val-offset.val := by omega
    rw [first]
    have dropNext : bytes.val.drop next.val=(bytes.val.drop offset.val).drop (next.val-offset.val) := by
      rw [List.drop_drop]
      congr 1
      omega
    rw [dropNext]
    have add : finish.val-offset.val=(next.val-offset.val)+(finish.val-next.val) := by omega
    rw [add,List.take_add]

/-- All returned source records partition the exact expanded input suffix;
the source's trailing-byte check supplies the endpoint. -/
theorem parsed_bytes (bytes : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (parsed : AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) :
    (pre.records.val.map (fun s => s.val)).flatten=bytes.val.drop 32 := by
  obtain ⟨_,finish,chain,last⟩ := ExtractedPrefixParse.parse_success bytes
    (AspisR1PublicPreparation.PrefixAdapter.toOld pre)
    (AspisR1PublicPreparation.PrefixAdapter.parse_success bytes pre parsed)
  have joined := chain_bytes chain
  change (pre.records.val.map (fun s => s.val)).flatten=_ at joined
  rw [last] at joined
  simpa only [show (32#usize).val=32 from rfl,←List.length_drop,List.take_length] using joined

#print axioms chain_bounds
#print axioms chain_bytes
#print axioms parsed_bytes
end AspisR1.PSem_RecordChain

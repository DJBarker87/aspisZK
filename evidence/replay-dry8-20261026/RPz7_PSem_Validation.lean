import RPz7_PSem_SourceRows
import PSem_FieldCanonical
set_option autoImplicit false
namespace AspisR1.PSem_Validation
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical
open ExtractedPrefixTrace

theorem length_encoding (n : Nat) : PublicInitFrame.lengthBytes n=le32 n := by
  apply List.ext_getElem
  · simp only [PublicInitFrame.lengthBytes,le32,List.length_ofFn,List.length_map,List.length_range]
  · intro i hi hj
    simp only [PublicInitFrame.lengthBytes,le32,List.getElem_ofFn,List.getElem_map,List.getElem_range]

def Logical (row : Nat) (b : Bytes) : Prop :=
  b.take 5=(⟨(rowShape row).1%256,Nat.mod_lt _ (by decide)⟩ :: le32 (rowShape row).2) ∧
    (14 ≤ row → canonical (b.drop 5))

def Checked : Nat → List Bytes → Prop
  | _,[] => True
  | row,b::bs => Logical row b ∧ Checked (row+1) bs

theorem source_record (row : U8) (frame payload : Slice U8)
    (h : AspisR1PrefixAggregateParser.r1_wire.parse_record row frame=ok (.Ok payload)) :
    Logical row.val (bytesOf frame.val) := by
  obtain ⟨tag,size,table,length,framed,_⟩ :=
    ExtractedPrefixFrameAgreement.parse_record_frame_success row frame payload h
  have valid : row.val<27 := by
    by_contra bad
    have none := ExtractedRowShape.row_shape_none row (Nat.le_of_not_gt bad)
    rw [ExtractedRowShape.row_shape_eq_table,table] at none
    cases none
  have sourceShape : AspisS1NativeCompact.r1_wire.row_shape row=ok (some (tag,size)) := by
    rw [PSem_Shapes.table_shape,table]
  have shape := PSem_Shapes.valid_shape row tag size valid sourceShape
  have tagEq : tag.val=(rowShape row.val).1 := congrArg Prod.fst shape
  have sizeEq : size.val=(rowShape row.val).2 := congrArg Prod.snd shape
  have model : RecordFrameCodec.parse (ExtractedRecordByteValue.rawByte tag) size.val
    (bytesOf frame.val)=some (bytesOf payload.val) := framed
  unfold RecordFrameCodec.parse at model
  split at model
  · rename_i checks
    have drop := Option.some.inj model
    refine ⟨?_,?_⟩
    · have tagBytes : ExtractedRecordByteValue.rawByte tag=
        (⟨(rowShape row.val).1%256,Nat.mod_lt _ (by decide)⟩ : Fin 256) := by
        apply Fin.ext
        change tag.val=(rowShape row.val).1%256
        rw [←tagEq,Nat.mod_eq_of_lt (by scalar_tac : tag.val<256)]
      simpa only [RecordFrameCodec.header,tagBytes,length_encoding,sizeEq,List.singleton_append] using checks.2
    · intro fieldRow
      rw [drop]
      exact PSem_FieldCanonical.source_payload row frame payload fieldRow h
  · cases model

theorem chain_checked {bytes : Slice U8} {rows : List U8} {offset finish : Usize}
    {frames : List (Slice U8)} (h : RecordChain bytes rows offset frames finish)
    (start : Nat) (order : rows.map UScalar.val=List.range' start rows.length) :
    Checked start (frames.map (fun s => bytesOf s.val)) := by
  induction h generalizing start with
  | nil => trivial
  | @cons row rows offset framed next frames finish step tail ih =>
    simp only [List.map_cons,List.length_cons,List.range'_succ] at order
    have rowEq := (List.cons.inj order).1
    have tailEq := (List.cons.inj order).2
    obtain ⟨tag,size,payload,_,_,_,_,parsed⟩ :=
      ExtractedPrefixRecordStep.parse_record_at_success bytes framed row offset next step
    exact ⟨by simpa only [rowEq] using source_record row framed payload parsed,ih (start+1) tailEq⟩

theorem parsed_checked (bytes : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (parsed : AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) :
    Checked 0 (pre.records.val.map (fun s => bytesOf s.val)) := by
  obtain ⟨_,finish,chain,_⟩ := ExtractedPrefixParse.parse_success bytes
    (AspisR1PublicPreparation.PrefixAdapter.toOld pre)
    (AspisR1PublicPreparation.PrefixAdapter.parse_success bytes pre parsed)
  exact chain_checked chain 0 rfl

#print axioms length_encoding
#print axioms source_record
#print axioms chain_checked
#print axioms parsed_checked
end AspisR1.PSem_Validation

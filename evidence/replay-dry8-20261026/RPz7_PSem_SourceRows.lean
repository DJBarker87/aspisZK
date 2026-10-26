import RPz7_PSem_RecordChain
import RPz7_PSem_Lengths
import ExtractedPrefixFrameAgreement
set_option autoImplicit false
namespace AspisR1.PSem_SourceRows
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical
open ExtractedPrefixTrace

theorem record_length (row : U8) (frame payload : Slice U8)
    (h : AspisR1PrefixAggregateParser.r1_wire.parse_record row frame=ok (.Ok payload)) :
    frame.val.length=5+(rowShape row.val).2 := by
  obtain ⟨tag,size,table,length,framed,_⟩ :=
    ExtractedPrefixFrameAgreement.parse_record_frame_success row frame payload h
  have valid : row.val<27 := by
    by_contra bad
    have none := ExtractedRowShape.row_shape_none row (Nat.le_of_not_gt bad)
    rw [ExtractedRowShape.row_shape_eq_table,table] at none
    cases none
  have sourceShape : AspisS1NativeCompact.r1_wire.row_shape row=ok (some (tag,size)) := by
    rw [PSem_Shapes.table_shape,table]
  have sizeEq := congrArg Prod.snd (PSem_Shapes.valid_shape row tag size valid sourceShape)
  have frameEq := ((RecordFrameCodec.parse_eq_some_iff _ _ _ _).mp framed).2
  have lengths := congrArg List.length frameEq
  simp only [List.length_map,RecordFrameCodec.frame_length] at lengths
  omega

theorem chain_lengths {bytes : Slice U8} {rows : List U8} {offset finish : Usize}
    {frames : List (Slice U8)} (h : RecordChain bytes rows offset frames finish)
    (start : Nat) (order : rows.map UScalar.val=List.range' start rows.length) :
    PSem_Lengths.Rows start (frames.map (fun s => bytesOf s.val)) := by
  induction h generalizing start with
  | nil => exact .nil _
  | @cons row rows offset framed next frames finish step tail ih =>
    simp only [List.map_cons,List.length_cons,List.range'_succ] at order
    have rowEq := (List.cons.inj order).1
    have tailEq := (List.cons.inj order).2
    obtain ⟨tag,size,payload,_,_,_,_,parsed⟩ :=
      ExtractedPrefixRecordStep.parse_record_at_success bytes framed row offset next step
    apply PSem_Lengths.Rows.cons
    · simpa only [bytesOf,List.length_map,rowEq] using record_length row framed payload parsed
    · exact ih (start+1) tailEq

theorem parsed_lengths (bytes : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (parsed : AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) :
    PSem_Lengths.Rows 0 (pre.records.val.map (fun s => bytesOf s.val)) := by
  obtain ⟨_,finish,chain,_⟩ := ExtractedPrefixParse.parse_success bytes
    (AspisR1PublicPreparation.PrefixAdapter.toOld pre)
    (AspisR1PublicPreparation.PrefixAdapter.parse_success bytes pre parsed)
  exact chain_lengths chain 0 rfl

/-- Exact complete27 returned source records, identified with compact-row
expansion on the original input. No arbitrary row-list agreement remains. -/
theorem source_records (input out expanded : Slice U8)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (expand : AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
      input out=ok (.Ok (),expanded))
    (parse : AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    PSem_Rows.expandRows 27 0 (bytesOf (input.val.drop 32))=
      some (pre.records.val.map (fun s => bytesOf s.val)) := by
  obtain ⟨rs,rows,joined⟩ := PSem_Expansion.source_rows input out expanded expand
  have raw := PSem_RecordChain.parsed_bytes expanded pre parse
  have logical : (pre.records.val.map (fun s => bytesOf s.val)).flatten=
      bytesOf (expanded.val.drop 32) := by
    simpa only [bytesOf,List.map_flatten,List.map_map,Function.comp_def] using congrArg bytesOf raw
  have same := PSem_Lengths.flatten_injective 0 rs _
    (PSem_Lengths.expanded_lengths 27 0 _ rs rows) (parsed_lengths expanded pre parse)
    (joined.symm.trans logical.symm)
  simpa only [same] using rows

#print axioms record_length
#print axioms chain_lengths
#print axioms parsed_lengths
#print axioms source_records
end AspisR1.PSem_SourceRows

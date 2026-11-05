import NIH_RecordFraming
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIX_DecodeFinish
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
/-- The original row-shape helper supplies the exact payload size, not just its cap. -/
theorem shape_size (row tag : U8) (size : Usize)
 (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size))) :
 size.val=NFU_PacketDomains.payloadSize row.val := by
 have h : NFQ_Reference.row_shape_ref row=ok (some (tag,size)) := by
  rw [NFQ_RowShape.prefix_reference]
  exact shape
 unfold NFQ_Reference.row_shape_ref at h
 split at h
 all_goals repeat' split at h
 all_goals simp only [Result.ok.injEq,Option.some.injEq,Prod.mk.injEq] at h
 all_goals rcases h with ⟨_,rfl⟩
 all_goals simp only [NFU_PacketDomains.payloadSize]
 all_goals scalar_tac

/-- This SAME framed record's passed predecessor guard discharges the former
framing input; the decoder may still return any exact WireError. -/
theorem framed (record : MainRecord) (payload : Slice U8)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.parse_record record.row record.framed=ok (.Ok payload)) :
 record.framed.val.length=5+NFU_PacketDomains.payloadSize record.row.val := by
 obtain ⟨tag,size,shape,length⟩:=NIH_RecordFraming.accepted record.row record.framed payload parsed
 rw [shape_size record.row tag size shape] at length
 exact length

theorem from_parser (N off : Usize) (record : MainRecord) (payload : Slice U8)
 (call : NGO_CallerDomains.Call record.row.val N.val off.val)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.parse_record record.row record.framed=ok (.Ok payload)) :
 record.framed.val.length≤3717 ∧
 32*off.val+32*N.val≤record.framed.val.length-5 ∧
 ∃ reply,decodeMain N record off=ok reply :=
 NIH_DecodeInstall.ready N off record call (framed record payload parsed)

theorem extra (record : MainRecord) (payload : Slice U8) (row : record.row.val=25)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.parse_record record.row record.framed=ok (.Ok payload)) :
 record.framed.val.length≤3717 ∧
 32*87+32*29≤record.framed.val.length-5 ∧
 ∃ reply,decodeMain 29#usize record 87#usize=ok reply := by
 apply from_parser 29#usize 87#usize record payload _ parsed
 rw [row]
 exact NGO_CallerDomains.Call.extra

theorem before_z1 (record : MainRecord) (payload : Slice U8) (row : record.row.val=26)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.parse_record record.row record.framed=ok (.Ok payload)) :
 record.framed.val.length≤3717 ∧
 32*0+32*29≤record.framed.val.length-5 ∧
 ∃ reply,decodeMain 29#usize record 0#usize=ok reply := by
 apply from_parser 29#usize 0#usize record payload _ parsed
 rw [row]
 exact NGO_CallerDomains.Call.beforeZ1
#print axioms shape_size
#print axioms framed
#print axioms from_parser
#print axioms extra
#print axioms before_z1
end AspisR1.NIX_DecodeFinish
end

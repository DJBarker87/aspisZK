import BinWireRecordLengths
import ExtractedRecordFraming

/-! Consequences of success of the retained source-extracted semantic parser.
The row_shape/parse_record bodies agree with the current row-length guards;
this is not a whole-prefix or deployed-transaction simulation theorem. -/
set_option autoImplicit false
namespace AspisR1.BinWireParsedLengths
open Aeneas Aeneas.Std Result

theorem table_sizes (row : U8) (tag : U8) (size : Usize)
    (h : ExtractedRowShape.table row = some (tag, size)) :
    size.val = 0 ∨ size.val = 32 ∨ size.val = 896 ∨
      size.val = 3712 ∨ size.val = 928 := by
  unfold ExtractedRowShape.table at h
  split_ifs at h <;> simp at h
  all_goals rcases h with ⟨_, rfl⟩ <;> norm_num

theorem parsed_record_lengths (row : U8) (record payload : Slice U8)
    (h : AspisR1RecordParser.r1_wire.parse_record row record =
      ok (core.result.Result.Ok payload)) :
    record.val.length = 5 ∨ record.val.length = 37 ∨ record.val.length = 901 ∨
      record.val.length = 3717 ∨ record.val.length = 933 := by
  obtain ⟨tag, size, _, _, _, _, ht, hl, _⟩ :=
    ExtractedRecordFraming.parse_record_success row record payload h
  have hs := table_sizes row tag size ht
  omega

theorem parsed_record_safe (row : U8) (record payload : Slice U8)
    (h : AspisR1RecordParser.r1_wire.parse_record row record =
      ok (core.result.Result.Ok payload)) :
    record.val.length ≠ 31 ∧ record.val.length ≠ 65 := by
  have hl := parsed_record_lengths row record payload h
  omega

theorem parsed_absorb_ne_node (row : U8) (record payload : Slice U8)
    (h : AspisR1RecordParser.r1_wire.parse_record row record =
      ok (core.result.Result.Ok payload))
    (toByte : U8 → BinMerkle32Path.Byte)
    (state : AspisV8R19.SourceDuplexStep.State) (cs : BinMerkle32Path.Children) :
    BinMerkle32Path.nodeInput cs ≠
      RawTranscriptFrameBytes.absorb state row.val (record.val.map toByte) := by
  apply BinWireRecordLengths.absorb_ne_node
  simpa only [List.length_map] using (parsed_record_safe row record payload h).1

#print axioms table_sizes
#print axioms parsed_record_lengths
#print axioms parsed_record_safe
#print axioms parsed_absorb_ne_node
end AspisR1.BinWireParsedLengths

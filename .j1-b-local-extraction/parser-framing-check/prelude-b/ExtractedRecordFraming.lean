import AspisR1RecordParser.Funs
import ExtractedRowShape

/-!
Framing consequences of success of the exact header-array parser extraction.
The field validator is not unfolded. No Rust execution, field-canonicality,
or prefix-refinement claim is made here.
-/
namespace AspisR1.ExtractedRecordFraming
open Aeneas Aeneas.Std Result

/-- Both kits contain the same exact row_shape declaration and constants. -/
theorem parser_row_shape_eq (row : U8) :
    AspisR1RecordParser.r1_wire.row_shape row =
      AspisR1RowShape.r1_wire.row_shape row := by
  unfold AspisR1RecordParser.r1_wire.row_shape AspisR1RowShape.r1_wire.row_shape
    AspisR1RecordParser.r1_wire.CLAIMS AspisR1RowShape.r1_wire.CLAIMS
    AspisR1RecordParser.r1_wire.POINTS AspisR1RowShape.r1_wire.POINTS
    AspisR1RecordParser.r1_wire.LANES AspisR1RowShape.r1_wire.LANES
  rfl

theorem parser_row_shape_table (row : U8) :
    AspisR1RecordParser.r1_wire.row_shape row =
      ok (ExtractedRowShape.table row) := by
  rw [parser_row_shape_eq, ExtractedRowShape.row_shape_eq_table]

private theorem bind_ok_iff {α β : Type} (m : Result α)
    (f : α → Result β) (y : β) :
    (m >>= f) = ok y ↔ ∃ x, m = ok x ∧ f x = ok y := by
  cases m <;> simp

private theorem index_ok_iff (record : Slice U8) (i : Usize) (x : U8) :
    Slice.index_usize record i = ok x ↔ record.val[i.val]? = some x := by
  unfold Slice.index_usize
  cases h : record[i]? <;> simp_all

private theorem add_ok_val (a b c : Usize) (h : a + b = ok c) :
    c.val = a.val + b.val := by
  have he := UScalar.add_equiv a b
  rw [h] at he
  exact he.2.1

/-- The same little-endian U32 decoder called by the generated parser. -/
def headerValue (b1 b2 b3 b4 : U8) : U32 :=
  core.num.U32.from_le_bytes (Array.make 4#usize [b1, b2, b3, b4])

/-- Concrete framing facts, including returned-slice equality and validation
success as a consequence, never as an added premise. -/
def SuccessfulFraming (row : U8) (record payload : Slice U8) : Prop :=
  ∃ tag size b1 b2 b3 b4,
    ExtractedRowShape.table row = some (tag, size) ∧
    record.val.length = 5 + size.val ∧
    record.val[0]? = some tag ∧
    record.val[1]? = some b1 ∧ record.val[2]? = some b2 ∧
    record.val[3]? = some b3 ∧ record.val[4]? = some b4 ∧
    (headerValue b1 b2 b3 b4).val = size.val ∧
    payload = record.drop 5#usize ∧
    payload.val.length = size.val ∧
    (14 ≤ row.val → AspisR1RecordParser.r1_wire.validate_record_fields row payload =
      ok (core.result.Result.Ok ()))

end AspisR1.ExtractedRecordFraming

#print axioms AspisR1.ExtractedRecordFraming.parser_row_shape_eq
#print axioms AspisR1.ExtractedRecordFraming.parser_row_shape_table

import PSem_Rows
import S1NativeCompactModelV1
import ExtractedRowShape
set_option autoImplicit false
namespace AspisR1.PSem_Shapes
open Aeneas Aeneas.Std Result

theorem source_shape (row : U8) :
    AspisS1NativeCompact.r1_wire.row_shape row =
      AspisR1RowShape.r1_wire.row_shape row := by
  unfold AspisS1NativeCompact.r1_wire.row_shape AspisR1RowShape.r1_wire.row_shape
  unfold AspisS1NativeCompact.r1_wire.CLAIMS AspisS1NativeCompact.r1_wire.POINTS
    AspisS1NativeCompact.r1_wire.LANES AspisR1RowShape.r1_wire.CLAIMS
    AspisR1RowShape.r1_wire.POINTS AspisR1RowShape.r1_wire.LANES
  rfl

theorem table_shape (row : U8) :
    AspisS1NativeCompact.r1_wire.row_shape row = ok (ExtractedRowShape.table row) := by
  rw [source_shape,ExtractedRowShape.row_shape_eq_table]

theorem valid_shape (row tag : U8) (size : Usize) (bound : row.val < 27)
    (h : AspisS1NativeCompact.r1_wire.row_shape row = ok (some (tag,size))) :
    (tag.val,size.val) = OraclePortCompactDraft.rowShape row.val := by
  rw [table_shape] at h
  have shape := Result.ok.inj h
  interval_cases hv : row.val <;>
    simp only [ExtractedRowShape.table,hv] at shape <;>
    norm_num at shape <;> rcases shape with ⟨rfl,rfl⟩ <;> simp [OraclePortCompactDraft.rowShape,hv]

theorem compact_flag (row : U8) :
    AspisS1NativeCompact.compact.compact_row row = ok (decide (14 ≤ row.val)) := by
  unfold AspisS1NativeCompact.compact.compact_row
  rfl

#print axioms source_shape
#print axioms table_shape
#print axioms valid_shape
#print axioms compact_flag
end AspisR1.PSem_Shapes

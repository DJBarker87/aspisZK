import AspisR1PrefixAggregateParser.Funs
import ExtractedRowShape
set_option autoImplicit false
namespace NDF_ParserDomain
open Aeneas Aeneas.Std Result

theorem shape_source (row : U8) :
    AspisR1PrefixAggregateParser.r1_wire.row_shape row = AspisR1RowShape.r1_wire.row_shape row := by
  unfold AspisR1PrefixAggregateParser.r1_wire.row_shape AspisR1RowShape.r1_wire.row_shape
  unfold AspisR1PrefixAggregateParser.r1_wire.CLAIMS AspisR1PrefixAggregateParser.r1_wire.POINTS
    AspisR1PrefixAggregateParser.r1_wire.LANES AspisR1RowShape.r1_wire.CLAIMS
    AspisR1RowShape.r1_wire.POINTS AspisR1RowShape.r1_wire.LANES
  rfl

theorem shape_bound (row tag : U8) (size : Usize)
    (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size))) :
    size.val≤3712 ∧ row.val<27 := by
  rw [shape_source,AspisR1.ExtractedRowShape.row_shape_eq_table] at shape
  have table := Result.ok.inj shape
  unfold AspisR1.ExtractedRowShape.table at table
  split_ifs at table <;> simp_all <;> scalar_tac

theorem framed_cap (row tag : U8) (size : Usize) (framed : Slice U8)
    (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size)))
    (length : framed.val.length=5+size.val) :
    framed.val.length≤3717 := by
  have bound := (shape_bound row tag size shape).1
  omega

#print axioms shape_source
#print axioms shape_bound
#print axioms framed_cap
end NDF_ParserDomain

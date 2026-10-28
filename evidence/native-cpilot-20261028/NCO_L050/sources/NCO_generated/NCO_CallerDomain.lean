import NCO_ParserShape
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_CallerDomain

theorem shape (row tag : U8) (size : Usize)
    (h : NCO_ParserRef.row_shape_ref row = ok (some (tag,size))) :
    size.val ≤ 3712 ∧ row.val < 27 := by
  rw [NCO_ParserShape.parser_shape,NCO_ParserShape.source_shape,
    AspisR1.ExtractedRowShape.row_shape_eq_table] at h
  have table := Result.ok.inj h
  unfold AspisR1.ExtractedRowShape.table at table
  split_ifs at table <;> simp_all <;> scalar_tac

theorem validator (row tag : U8) (size : Usize) (record1 payload : Slice U8)
    (h : NCO_ParserRef.row_shape_ref row = ok (some (tag,size)))
    (framing : record1.val.length = 5+size.val)
    (slice : payload.val = record1.val.drop 5) : payload.val.length ≤ 3712 := by
  have bound := (shape row tag size h).1
  rw [slice,List.length_drop,framing]
  omega

#print axioms shape
#print axioms validator
end NCO_CallerDomain

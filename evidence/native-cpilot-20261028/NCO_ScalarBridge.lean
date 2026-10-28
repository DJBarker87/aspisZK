import NCO_Reference.Funs
import S1NativeCompactModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_ScalarBridge

theorem compact_row (row : U8) :
    NCO_Reference.compact_row_ref row = AspisS1NativeCompact.compact.compact_row row := by
  rfl

theorem row_shape (row : U8) :
    NCO_Reference.row_shape_ref row = AspisS1NativeCompact.r1_wire.row_shape row := by
  by_cases h0 : row = 0#u8
  · subst row; rfl
  by_cases h1 : row = 1#u8
  · subst row; rfl
  by_cases h2 : row = 2#u8
  · subst row; rfl
  by_cases h14 : row = 14#u8
  · subst row; rfl
  by_cases h25 : row = 25#u8
  · subst row; rfl
  by_cases h26 : row = 26#u8
  · subst row; rfl
  simp [NCO_Reference.row_shape_ref, AspisS1NativeCompact.r1_wire.row_shape,
    h0, h1, h2, h14, h25, h26]

#print axioms compact_row
#print axioms row_shape
end NCO_ScalarBridge

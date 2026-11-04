import Aeneas
set_option autoImplicit false
namespace NEW_ShiftLiteral
open Aeneas Aeneas.Std
/-- The ill-typed generated RHS and the library's U32 RHS denote the SAME
positive shift count. This is a literal type repair, not a changed shift. -/
theorem signed_unsigned_nine : (9#i32).val = ((9#u32).val : Int) := by decide

theorem valid_count : (9#u32).val < 64 := by decide

#print axioms signed_unsigned_nine
#print axioms valid_count
end NEW_ShiftLiteral

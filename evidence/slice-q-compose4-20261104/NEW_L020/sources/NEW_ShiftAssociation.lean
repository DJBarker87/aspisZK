import NEW_GeometryActual.Funs
import NEW_ShiftLiteral
set_option autoImplicit false
namespace NEW_ShiftAssociation
open Aeneas Aeneas.Std Result

theorem checked_to_wrapping (u : Usize) :
    (u >>> 9#i32 : Result Usize) = ok (Usize.wrapping_shr u 9#u32) := by
  rfl

#print axioms checked_to_wrapping
end NEW_ShiftAssociation

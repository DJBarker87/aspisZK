import NCX_Reference.Funs
set_option autoImplicit false
namespace NCX_Status
open Aeneas Aeneas.Std Result

theorem active : NCX_Reference.status 1#u8=ok (.Ok .Active) := by
  simp [NCX_Reference.status]
#print axioms active
end NCX_Status

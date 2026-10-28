import NCX_Reference.Funs
set_option autoImplicit false
namespace NCX_Status
open Aeneas Aeneas.Std Result

theorem active : NCX_Reference.status 1#u8=ok (.Ok .Active) := by
  unfold NCX_Reference.status
  split <;> first | rfl | scalar_tac
#print axioms active
end NCX_Status

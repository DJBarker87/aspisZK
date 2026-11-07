import NMB_TypedTrace
import NLD_TraceControl
set_option autoImplicit false
namespace NMB_TypedControl
open Aeneas Aeneas.Std Result NMB_TypedTrace
theorem forget_control {A B C : Type} (value : core.ops.control_flow.ControlFlow B C)
 (advance : C → Run A) (reject : B → Run A) :
 forget (match value with | .Continue c=>advance c | .Break b=>reject b)=
 match value with | .Continue c=>forget (advance c) | .Break b=>forget (reject b) := by
 cases value <;> rfl
#print axioms forget_control
end NMB_TypedControl

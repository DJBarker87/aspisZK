import PV_L1D_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace PV_L1D_EraseControl
open PV_L1D_Logged
open Aeneas Aeneas.Std ProverRwFull
/-- Push erasure through a control-flow match symbolically, without reducing
any of the proof data or the selected continuation. -/
theorem control {A B C : Type} (x : core.ops.control_flow.ControlFlow A B)
    (f : B → Logged C) (g : A → Logged C) :
    erase (match x with | .Continue b => f b | .Break a => g a) =
      match x with | .Continue b => erase (f b) | .Break a => erase (g a) := by
  cases x <;> rfl
#print axioms control
end PV_L1D_EraseControl

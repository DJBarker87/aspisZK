import NLD_SourceTrace
set_option autoImplicit false
namespace AspisR1.NLD_SourceTrace
open Aeneas Aeneas.Std Result
/-- Projection through a complete Rust ?-branch; neither arm is discarded. -/
theorem erase_control {A B C : Type} (value : core.ops.control_flow.ControlFlow B C)
    (continue : C → Trace A) (reject : B → Trace A) :
    (match value with
      | .Continue c => continue c
      | .Break b => reject b).2 =
    match value with
      | .Continue c => (continue c).2
      | .Break b => (reject b).2 := by cases value <;> rfl
#print axioms erase_control
end AspisR1.NLD_SourceTrace

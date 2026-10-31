import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard20
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (linkIndex : Nat) (h : Emitted 136 linkIndex) :
 linkIndex < 136 := by
  exact h.2
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard20

import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard331
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (lane : Nat) (h : Emitted 16 lane) :
 lane < 16 := by
  exact h.2
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard331

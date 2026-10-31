import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard14
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (point column : Nat) (hp : point < 3) (hc : column < 28) :
 point*28+column < 84 := by
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard14

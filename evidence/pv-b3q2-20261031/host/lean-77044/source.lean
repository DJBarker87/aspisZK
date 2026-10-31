import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard60
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (row : Nat) (h : row < 1024) :
 row/16 < 64 ∧ row%16 < 16 := by
  exact PV_B3Q_PanicGuards.endpoint_selector_bounds row h
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard60

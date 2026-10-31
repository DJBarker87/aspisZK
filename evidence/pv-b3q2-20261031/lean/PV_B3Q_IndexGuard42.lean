import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard42
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (lower upper index : Nat) (h : Reach lower upper index) (active : index < upper) (caller : upper ≤ 64) :
 index < 64 := by
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard42

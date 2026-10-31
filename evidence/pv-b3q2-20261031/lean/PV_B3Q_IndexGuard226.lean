import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard226
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
def constantReads : List (Nat × Nat) := [(9,16)]
theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide
#print axioms constant_bounds
theorem dynamic_bounds (before : Nat) (h : before ≤ 9) (positive : 0 < before) :
 before-1 < 16 := by
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard226

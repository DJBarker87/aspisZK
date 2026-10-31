import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard38
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
def constantReads : List (Nat × Nat) := [(0,8),(1,8),(2,8),(3,8),(4,8),(5,8),(6,8),(7,8)]
theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide
#print axioms constant_bounds
theorem dynamic_bounds (level : Nat) (h : Reach 0 20 level) :
 level < 21 := by
  have b := reach_invariant h
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard38

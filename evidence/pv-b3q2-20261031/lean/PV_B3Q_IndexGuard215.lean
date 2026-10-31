import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard215
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
def constantReads : List (Nat × Nat) := [(0,3),(1,3),(2,3),(0,3),(1,3),(2,3),(0,3),(1,3),(2,3),(0,3),(1,3),(2,3)]
theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide
#print axioms constant_bounds
theorem dynamic_bounds (lane : Nat) (h : Emitted 16 lane) :
 lane < 16 := by
  exact h.2
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard215

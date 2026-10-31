import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard310
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
def constantReads : List (Nat × Nat) := [(0,4),(1,4),(2,4),(3,4)]
theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide
#print axioms constant_bounds
theorem dynamic_bounds (group : Nat) (h : Emitted 4 group) :
 4*group < 16 ∧ 4*group+1 < 16 ∧ 4*group+2 < 16 ∧ 4*group+3 < 16 ∧ group < 4 := by
  have b := h.2
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard310

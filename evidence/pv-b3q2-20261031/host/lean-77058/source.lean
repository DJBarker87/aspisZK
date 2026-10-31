import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard224
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
def constantReads : List (Nat × Nat) := [(0,16),(0,17)]
theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide
#print axioms constant_bounds
theorem dynamic_bounds (lane : Nat) (h : Emitted 8 lane) :
 1+lane < 16 ∧ lane < 16 ∧ 1+lane < 17 ∧ 8+lane < 16 ∧ 1+8+lane < 17 := by
  have b := h.2
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard224

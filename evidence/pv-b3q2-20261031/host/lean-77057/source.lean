import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard223
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
def constantReads : List (Nat × Nat) := [(0,64),(1,64),(25,64),(30,64),(27,64),(28,64),(29,64),(0,16),(0,16),(1,64),(30,64),(0,64),(25,64),(0,64),(25,64),(0,16),(0,16),(0,64),(1,64),(2,64),(25,64),(26,64),(30,64),(31,64),(3,64),(32,64),(12,16)]
theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide
#print axioms constant_bounds
theorem dynamic_bounds (lane : Nat) (h : Emitted 16 lane) :
 lane < 16 ∧ 8 < 16 ∧ 8+1 < 16 := by
  have b := h.2
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard223

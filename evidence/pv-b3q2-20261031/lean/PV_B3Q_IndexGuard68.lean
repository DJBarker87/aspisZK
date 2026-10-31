import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard68
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
def constantReads : List (Nat × Nat) := [(0,2),(1,2),(0,2),(1,2),(0,4),(1,4),(2,4),(3,4),(0,2),(1,4),(1,2),(0,4),(0,2),(3,4),(1,2),(2,4)]
theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide
#print axioms constant_bounds
end PV_B3Q_IndexGuard68

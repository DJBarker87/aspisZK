import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard430
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
def constantReads : List (Nat × Nat) := [(0,4),(0,4),(1,4),(1,4),(2,4),(2,4),(2,4),(3,4),(3,4),(2,4),(3,4),(3,4),(0,4),(1,4),(1,4),(0,4),(2,4),(2,4),(2,4),(3,4),(3,4),(2,4),(3,4),(3,4),(0,4),(2,4),(1,4),(3,4),(2,4),(0,4),(3,4),(1,4),(0,4),(3,4),(1,4),(2,4),(2,4),(1,4),(3,4),(0,4),(0,4),(1,4),(2,4),(3,4)]
theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide
#print axioms constant_bounds
theorem dynamic_bounds (output limb : Nat) (ho : Emitted 4 output) (hl : Emitted 4 limb) :
 output < 4 ∧ limb < 4 ∧ (output=0 ∨ output=1 ∨ output=2 ∨ output=3) := by
  have o := ho.2
  have l := hl.2
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard430

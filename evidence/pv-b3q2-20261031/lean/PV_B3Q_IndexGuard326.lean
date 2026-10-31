import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard326
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
def constantReads : List (Nat × Nat) := [(0,16),(0,16)]
theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide
#print axioms constant_bounds
theorem dynamic_bounds (lane limb : Nat) (hl : Emitted 16 lane) (hb : Emitted 4 limb) :
 lane < 16 ∧ limb < 4 := by
  exact ⟨hl.2,hb.2⟩
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard326

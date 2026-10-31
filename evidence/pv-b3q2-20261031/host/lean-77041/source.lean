import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard55
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
def constantReads : List (Nat × Nat) := [(0,3),(1,3),(2,3),(10,16),(30,33),(10,16),(31,33),(10,16),(32,33),(0,16),(1,16),(2,16),(0,16),(1,16)]
theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide
#print axioms constant_bounds
theorem dynamic_bounds (rangeIndex conserveIndex : Nat) (hr : Emitted 10 rangeIndex) (hc : Emitted 10 conserveIndex) :
 rangeIndex < 16 ∧ 10+rangeIndex < 33 ∧ conserveIndex < 16 ∧ 20+conserveIndex < 33 := by
  have r := hr.2
  have c := hc.2
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard55

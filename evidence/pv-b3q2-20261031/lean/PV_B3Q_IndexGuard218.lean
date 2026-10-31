import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard218
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
def constantReads : List (Nat × Nat) := [(0,4),(0,4),(1,4),(1,4),(2,4),(2,4),(3,4),(3,4),(0,4),(1,4),(2,4),(3,4),(0,4),(0,4),(1,4),(1,4),(2,4),(2,4),(3,4),(3,4),(0,4),(1,4),(2,4),(3,4)]
theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide
#print axioms constant_bounds
theorem dynamic_bounds (start index finish limb : Nat) (outer : start < finish) (inner : start ≤ index) (guard : index < min (start+4) finish) (limbGuard : Emitted 4 limb) :
 index < finish ∧ index-start < 4 ∧ limb < 4 := by
  have b := chunk_bounds start index finish outer inner guard
  exact ⟨b.1,b.2,limbGuard.2⟩
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard218

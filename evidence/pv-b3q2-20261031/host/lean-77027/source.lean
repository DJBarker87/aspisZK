import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard0
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (i : Nat) (h : Emitted 84 i) :
 i / 28 < 3 ∧ i % 28 < 29 ∧ i < 84 := by
  have b := h.2
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard0

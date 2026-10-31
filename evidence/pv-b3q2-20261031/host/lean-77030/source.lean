import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard13
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (level : Nat) (h : Emitted 20 level) :
 level < 20 ∧ level < 64 := by
  have b := h.2
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard13

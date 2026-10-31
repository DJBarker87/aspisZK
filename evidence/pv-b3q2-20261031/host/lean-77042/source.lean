import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard57
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (level carry : Nat) (h : Emitted 20 level) (branch : carry < 20) :
 level < 20 ∧ carry < 20 ∧ 34+level < 64 := by
  have b := h.2
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard57

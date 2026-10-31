import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard6
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (column maskColumn before24 before4 : Nat) (h16 : Emitted 16 column) (h10 : Emitted 10 maskColumn) (h24 : before24 ≤ 24) (p24 : 0 < before24) (h4 : before4 ≤ 4) (p4 : 0 < before4) :
 column < 16 ∧ maskColumn < 10 ∧ 16+maskColumn < 28 ∧ before24-1 < 24 ∧ before4-1 < 4 := by
  have b := h16.2
  have c := h10.2
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard6

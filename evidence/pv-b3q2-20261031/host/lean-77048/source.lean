import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard185
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (coordinate len index : Nat) (h : PV_B3Q_ExpandGuards.Stage 0 coordinate len) (outer : coordinate < 6) (inner : index < len) :
 coordinate < 10 ∧ index < 64 ∧ 2*index < 64 ∧ 2*index+1 < 64 := by
  exact PV_B3Q_ExpandGuards.high_inner coordinate len index h outer inner
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard185

import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard58
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (start count group slot : Nat) (shape : 0 < count ∧ start+count ≤ 96) (groupBound : group ≤ (start+count-1)/4) (slotBound : slot < 4) (inside : start ≤ 4*group+slot ∧ 4*group+slot < start+count) :
 group < 24 ∧ slot < 4 ∧ 4*group+slot-start < count := by
  exact preweighted_source start count group slot shape groupBound slotBound inside
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard58

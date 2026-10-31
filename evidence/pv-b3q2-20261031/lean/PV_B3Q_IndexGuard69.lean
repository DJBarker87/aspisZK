import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard69
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (link : PV_B3Q_FrozenTables.Link) (h : link ∈ PV_B3Q_FrozenTables.links) :
 link.2.2.1.2.1 < 2 ∧ link.2.2.1.2.2 < 14 ∧ link.2.2.2.2.1 < 2 ∧ link.2.2.2.2.2 < 14 := by
  have b := PV_B3Q_FrozenTables.link_member_safe link h
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard69

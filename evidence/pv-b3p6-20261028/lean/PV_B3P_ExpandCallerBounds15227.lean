import PV_B3P_Operations12227
import PV_B3P_ReverseRange14227
namespace PV_B3P_Caller15227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- Both actual selector-expansion calls use a complete point slice. -/
theorem expand_point_slices15 (point : Array aspis_core.field.QM31 10#usize) :
    (point.val.take 6).length = 6 ∧ (point.val.drop 6).length = 4 := by
  simp only [List.length_take,List.length_drop,point.property]
  decide

theorem expand_two_write_bounds15 (index len capacity : Nat)
    (source_bound : index < len) (space : 2*len ≤ capacity) :
    2*index < capacity ∧ 2*index+1 < capacity := by omega

/-- A decreasing source index reads the parent before it overwrites either
child. The two children are distinct; no next smaller parent is overwritten. -/
theorem expand_reverse_frame15 (index smaller : Nat) (next : smaller < index) :
    smaller ≠ 2*index ∧ smaller ≠ 2*index+1 ∧ 2*index ≠ 2*index+1 := by omega
#print axioms expand_point_slices15
#print axioms expand_two_write_bounds15
#print axioms expand_reverse_frame15
end PV_B3P_Caller15227

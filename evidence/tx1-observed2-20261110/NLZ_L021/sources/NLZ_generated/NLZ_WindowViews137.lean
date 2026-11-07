import NLZ_Geometry137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_WindowViews137
open Aeneas Aeneas.Std AspisR1.NLZ_Resources
/-- Original-allocation record interpretation, with initialized payload bytes.
The Kani metadata and byte-frame windows must establish these premises at
SAME cuts before this can transport an actual Prefix. -/
theorem record (h : Heap) (original : Window) (bytes : List U8)
 (view : View h original bytes) (extent : original.length=13831)
 (j : Nat) (row : j<27) :
 View h (subwindow original (NLZ_Geometry137.offset j) (NLZ_Geometry137.width j))
 ((bytes.drop (NLZ_Geometry137.offset j)).take (NLZ_Geometry137.width j)) := by
 apply subview h original bytes _ _ view
 rw [extent]
 exact NLZ_Geometry137.within j row
theorem root (h : Heap) (original : Window) (bytes : List U8)
 (view : View h original bytes) (extent : original.length=13831) :
 View h (subwindow original 0 32) (bytes.take 32) := by
 have part := subview h original bytes 0 32 view (by rw [extent];omega)
 simpa only [List.drop_zero] using part
#print axioms record
#print axioms root
end AspisR1.NLZ_WindowViews137
end

import NMB_ThreeSnapshots
set_option autoImplicit false
noncomputable section
namespace NMB_FirstIndex
open Aeneas Aeneas.Std Result AspisR1
/-- The child receives the SAME array returned by the snapshot fold. -/
theorem source (x : NMB_Input.Input) :
 Slice.index_usize (NMB_ThreeSnapshots.first x) 0#usize = .ok (x.snapshot 0 58295 58295) ∧
 Slice.index_usize (NMB_ThreeSnapshots.first x) 1#usize = .ok (x.snapshot 1 1880 1880) ∧
 Slice.index_usize (NMB_ThreeSnapshots.first x) 2#usize = .ok (x.snapshot 2 1768 1768) :=
 ⟨rfl,rfl,rfl⟩
#print axioms source
end NMB_FirstIndex

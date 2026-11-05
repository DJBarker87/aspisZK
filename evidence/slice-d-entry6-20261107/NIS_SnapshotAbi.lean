import S2W_D189Wrappers
set_option autoImplicit false
namespace AspisR1.NIS_SnapshotAbi
open Aeneas Aeneas.Std S2W_D189Entry S2W_D189Wrappers

/-- Exactly the ten source arguments checked by the native ABI cuts. -/
theorem first_sizes : firstSizes 0 = (58295,58295) ∧
    firstSizes 1 = (1880,1880) ∧ firstSizes 2 = (1768,1768) := by
  exact ⟨rfl,rfl,rfl⟩

theorem second_sizes : secondSizes 0 = (58295,58295) ∧
    secondSizes 1 = (384,384) ∧ secondSizes 2 = (192,192) ∧
    secondSizes 3 = (768,768) ∧ secondSizes 4 = (128,256) ∧
    secondSizes 5 = (192,320) ∧ secondSizes 6 = (1768,1768) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem first_records (e : Entry) : e.first.val =
    [e.snapshot 0 58295 58295,e.snapshot 1 1880 1880,e.snapshot 2 1768 1768] := rfl

theorem second_records (e : Entry) : (e.second secondSizes).val =
    [e.snapshot 0 58295 58295,e.snapshot 1 384 384,e.snapshot 2 192 192,
     e.snapshot 3 768 768,e.snapshot 4 128 256,e.snapshot 5 192 320,
     e.snapshot 6 1768 1768] := rfl

#print axioms first_sizes
#print axioms second_sizes
#print axioms first_records
#print axioms second_records
end AspisR1.NIS_SnapshotAbi

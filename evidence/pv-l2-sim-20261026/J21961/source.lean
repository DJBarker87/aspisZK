import R1Z.PV_L2_RecordRefinement
import R1Z.PV_L2_F6HalfShift

set_option autoImplicit false
namespace R1Z.PV_L2_F6HalfInputs
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def source (a h : Slice U32) : Result ((U32 × U32 × U32 × U32) × (U32 × U32 × U32 × U32)) := do
  let x01 ← PV_L2_F6HalfShift.source a
  let x1 ← Slice.index_usize a 1#usize
  let x2 ← Slice.index_usize a 2#usize
  let x3 ← Slice.index_usize a 3#usize
  let y0 ← Slice.index_usize h 0#usize
  let y1 ← Slice.index_usize h 1#usize
  let y2 ← Slice.index_usize h 2#usize
  let y3 ← Slice.index_usize h 3#usize
  ok ((x01,x1,x2,x3),(y0,y1,y2,y3))
def recorded (a h : Slice U32) : Recorded ((U32 × U32 × U32 × U32) × (U32 × U32 × U32 × U32)) := do
  let x01 ← PV_L2_F6HalfShift.recorded a
  let x1 ← operation (.index 0 (1#usize).val) (Slice.index_usize a 1#usize)
  let x2 ← operation (.index 0 (2#usize).val) (Slice.index_usize a 2#usize)
  let x3 ← operation (.index 0 (3#usize).val) (Slice.index_usize a 3#usize)
  let y0 ← operation (.index 1 (0#usize).val) (Slice.index_usize h 0#usize)
  let y1 ← operation (.index 1 (1#usize).val) (Slice.index_usize h 1#usize)
  let y2 ← operation (.index 1 (2#usize).val) (Slice.index_usize h 2#usize)
  let y3 ← operation (.index 1 (3#usize).val) (Slice.index_usize h 3#usize)
  PV_L2_Record.pure ((x01,x1,x2,x3),(y0,y1,y2,y3))
theorem erases (a h : Slice U32) : (recorded a h).value = source a h := by
  simp only [recorded,source,PV_L2_RecordCompact.bind_value,
    PV_L2_F6HalfShift.erases,PV_L2_RecordCompact.operation_bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]
#print axioms erases
end R1Z.PV_L2_F6HalfInputs

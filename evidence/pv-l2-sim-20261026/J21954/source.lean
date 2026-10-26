import R1Z.PV_L2_RecordRefinement

set_option autoImplicit false
namespace R1Z.PV_L2_F6HalfShift
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def source (a : Slice U32) : Result (U32) := do
  let i ← Slice.index_usize a 0#usize
  let i1 ← lift (UScalar.cast .U64 i)
  let i2 ← i1 % P
  let i3 ← i2 + P
  let i4 ← i3 - 1073741824#u64
  let x0 ← i4 % P
  let x01 ← lift (UScalar.cast .U32 x0)
  ok x01
def recorded (a : Slice U32) : Recorded (U32) := do
  let i ← operation (.index 0 (0#usize).val) (Slice.index_usize a 0#usize)
  let i1 := UScalar.cast .U64 i
  let i2 ← operation (.rem i1.val P.val) (i1 % P)
  let i3 ← operation (.add i2.val P.val) (i2 + P)
  let i4 ← operation (.guard 31 i3.val (1073741824#u64).val true) (i3 - 1073741824#u64)
  let x0 ← operation (.rem i4.val P.val) (i4 % P)
  let x01 := UScalar.cast .U32 x0
  PV_L2_Record.pure x01
theorem erases (a : Slice U32) : (recorded a).value = source a := by
  simp only [recorded,source,PV_L2_RecordCompact.bind_value,
    PV_L2_RecordCompact.operation_bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]
#print axioms erases
end R1Z.PV_L2_F6HalfShift

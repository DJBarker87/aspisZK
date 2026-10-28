import R1Z.PV_CBL_AppendSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RL_V182
set_option autoImplicit false
/-- Exact push_str byte-body call, including the complete modeled Result. -/
def nativeBytes (s : alloc.vec.Vec U8) (t : Slice U8) : Result (alloc.vec.Vec U8) :=
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 s t
theorem complete (s : alloc.vec.Vec U8) (t : Slice U8) :
    nativeBytes s t=PV_CBL_StringPushBytes.push_bytes_reference s t := rfl
/-- Retain all size/UTF8 branches of the existing String carrier adapter. -/
def nativeAdapter (s : String) (t : Str) : Result String := do
  let v ← PV_CBL_StringBytesAdapter.encode s
  let v ← nativeBytes v t
  PV_CBL_StringBytesAdapter.decode v
theorem adapter (s : String) (t : Str) :
    nativeAdapter s t=PV_CBL_StringBytesAdapter.append s t := rfl
theorem nonvacuous :
    nativeBytes (alloc.vec.Vec.new U8) (Slice.new U8)=ok (alloc.vec.Vec.new U8) := by
  rfl
#print axioms complete
#print axioms adapter
#print axioms nonvacuous
end R1Z.PV_RL_V182

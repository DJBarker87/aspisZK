import R1Z.PV_CBL_JoinSlices
import R1Z.PV_CBL_StringByteObservation
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_JoinAdapter
set_option autoImplicit false
/-- Complete Result adapter on the existing valid-UTF8 path carrier. Native
P6 bounds, arbitrary-PathBuf image and allocation/world association stay explicit. -/
def reference (base path : String) : Result String := do
  let b ← PV_CBL_StringBytesAdapter.encode base
  let p ← PV_CBL_StringBytesAdapter.encode path
  let out ← PV_CBL_JoinSlices.join_slices_reference
    (alloc.vec.Vec.deref b) (alloc.vec.Vec.deref p) (alloc.vec.Vec.new U8)
  PV_CBL_StringBytesAdapter.decode out
theorem decode_output (native : String) (out : alloc.vec.Vec U8)
    (h : out.val=PV_CBL_StringBytesAdapter.encodeList native) :
    PV_CBL_StringBytesAdapter.decode out=ok native := PV_CBL_StringByteObservation.decode_of_bytes native out h
#print axioms reference
#print axioms decode_output
end R1Z.PV_CBL_JoinAdapter

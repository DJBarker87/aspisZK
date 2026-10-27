import R1Z.PV_CBL_PathJoinValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PathJoinChecked
set_option autoImplicit false

/-- Checked value specification, not an extracted allocation/Drop/native law. -/
def reference (base path : Slice U8) : Result (alloc.vec.Vec U8) :=
  let out := PV_CBL_PathJoinValue.join base.val path.val
  if h : out.length≤Usize.max then ok ⟨out,h⟩ else fail .maximumSizeExceeded

#print axioms reference
end R1Z.PV_CBL_PathJoinChecked

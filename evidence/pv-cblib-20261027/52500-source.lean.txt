import Aeneas
import R1Z.PV_CBL_ArrayKernel
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBL_ArraySliceResult
def array_slice_result_reference
  {T : Type} (N : Std.Usize) (coremarkerCopyInst : core.marker.Copy T)
  (v : Slice T) (zero : T) :
  Result (core.result.Result (Array T N) (alloc.vec.Vec T))
  := do
  let o ← PV_CBL_ArrayKernel.array_reference N coremarkerCopyInst v zero
  match o with
  | none =>
    let v1 ← alloc.slice.Slice.to_vec coremarkerCopyInst.cloneInst v
    ok (core.result.Result.Err v1)
  | some out => ok (core.result.Result.Ok out)

#print axioms array_slice_result_reference
end PV_CBL_ArraySliceResult

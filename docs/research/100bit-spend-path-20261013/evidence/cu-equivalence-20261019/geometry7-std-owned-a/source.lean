import Aeneas
set_option autoImplicit false
noncomputable section
namespace AspisR1GeometryStd
open Aeneas Aeneas.Std Result ControlFlow
def core.result.Result.map_err {T E F O : Type}
    (callback : core.ops.function.FnOnce O E F)
    (self : core.result.Result T E) (op : O) : Result (core.result.Result T F) := do
  match self with
  | .Ok value => .ok (.Ok value)
  | .Err err =>
    let mapped ← callback.call_once op err
    .ok (.Err mapped)

namespace CallerTraversal

def anyBody {I T F : Type} (next : I → Result (Option T × I))
    (call : F → T → Result (Bool × F)) (state : I × F) :
    Result (ControlFlow (I × F) (Bool × I)) := do
  let (item, iter) ← next state.1
  match item with
  | none => .ok (.done (false, iter))
  | some x =>
    let (hit, callback) ← call state.2 x
    if hit then .ok (.done (true, iter)) else .ok (.cont (iter, callback))

def anyRun {I T F : Type} (next : I → Result (Option T × I))
    (call : F → T → Result (Bool × F)) (iter : I) (callback : F) : Result (Bool × I) :=
  loop (anyBody next call) (iter, callback)

end CallerTraversal

def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
    {T F : Type} (callback : core.ops.function.FnMut F T Bool)
    (self : core.slice.iter.Iter T) (f : F) : Result (Bool × core.slice.iter.Iter T) :=
  CallerTraversal.anyRun Aeneas.Std.core.slice.iter.IteratorSliceIter.next callback.call_mut self f

#print axioms core.result.Result.map_err
#print axioms core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
end AspisR1GeometryStd

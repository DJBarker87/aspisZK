import Aeneas
import AspisR1ViewParseProbe.Types

/-! Explicit library models for the used H caller externals. Option.ok_or
and Result.map_err reuse the existing extracted library definitions. The
slice/array comparisons implement the pinned Rust as_array length split and
delegate to the existing Aeneas array comparison model. SliceIter.any reuses
TraversalRuntime's next-based model; the pinned Rust slice specialization is
also a next-based while loop. The unused generic Iterator.any.default and the
opaque query helper are omitted from this caller-only dependency cone.
These are stated library-model boundaries, not compiler correctness proofs.
-/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace AspisR1ViewParseProbe

def Slice.Insts.CoreCmpPartialEqArray.eq
    {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
    (self : Slice T) (other : Array U N) : Result Bool :=
  if h : self.val.length = N.val then
    Aeneas.Std.core.array.equality.PartialEqArray.eq cmp ⟨self.val, h⟩ other
  else .ok false

def Slice.Insts.CoreCmpPartialEqArray.ne
    {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
    (self : Slice T) (other : Array U N) : Result Bool :=
  if h : self.val.length = N.val then
    Aeneas.Std.core.array.equality.PartialEqArray.ne cmp ⟨self.val, h⟩ other
  else .ok true

def core.option.Option.ok_or {T E : Type} (self : Option T) (err : E) :
    Result (core.result.Result T E) :=
  match self with
  | some value => .ok (.Ok value)
  | none => .ok (.Err err)

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

#print axioms Slice.Insts.CoreCmpPartialEqArray.eq
#print axioms Slice.Insts.CoreCmpPartialEqArray.ne
#print axioms core.option.Option.ok_or
#print axioms core.result.Result.map_err
#print axioms core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any

end AspisR1ViewParseProbe

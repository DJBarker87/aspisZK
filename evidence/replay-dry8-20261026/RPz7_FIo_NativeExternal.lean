import RPz7_FIo_NativeTypes
import FIo_QRawFuns
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace FIo_Native
/-- Explicit allocator interpretation; no success property is bundled here. -/
class Allocation where
  reserve : {T : Type} → (A : Type) → alloc.vec.Vec T → Usize →
    Result ((core.result.Result Unit alloc.collections.TryReserveError) × alloc.vec.Vec T)

def alloc.vec.Vec.try_reserve_exact {T : Type} [a : Allocation]
    (A : Type) (self : alloc.vec.Vec T) (n : Usize) :
    Result ((core.result.Result Unit alloc.collections.TryReserveError) × alloc.vec.Vec T) :=
  a.reserve A self n

def fast_pairing.canonical.Q.raw (self rhs : fast_pairing.canonical.Q) :
    Result (Array U64 4#usize) := FIo_QRaw.canonical.Q.raw self rhs

/-- [core::result::{core::result::Result<T, E>}::map_err]:
    Source: '/rustc/library/core/src/result.rs', lines 962:4-964:53
    Name pattern: [core::result::{core::result::Result<@T, @E>}::map_err]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
  {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F) (self : core.result.Result T E) (op : O) :
  Result (core.result.Result T F)
  := do
  match self with
  | core.result.Result.Ok t => ok (core.result.Result.Ok t)
  | core.result.Result.Err e =>
    let t ← opsfunctionFnOnceOTupleEFInst.call_once op e
    ok (core.result.Result.Err t)



end FIo_Native

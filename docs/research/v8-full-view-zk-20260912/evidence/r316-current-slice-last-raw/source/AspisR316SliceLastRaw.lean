import Aeneas.Std
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR316SliceLastRaw

/-- [core::slice::{[T]}::last]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 281:4-281:42
    Name pattern: [core::slice::{[@T]}::last]
    Visibility: public -/
@[rust_fun "core::slice::{[@T]}::last"]
def core.slice.Slice.last {T : Type} (self : Slice T) : Result (Option T) := do
  let i := Slice.len self
  if i >= 1#usize
  then
    let i1 := Slice.len self
    let i2 ← UScalar.sub i1 1#usize
    let last ← Slice.index_usize self i2
    ok (some last)
  else ok none

#print axioms core.slice.Slice.last

end AspisR316SliceLastRaw

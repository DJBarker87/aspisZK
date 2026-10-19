-- Exact selected emitted declaration; body unchanged.
import AspisR1CuArraySource.Primitives
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1CuArraySource
/-- [core::array::{core::array::Guard<'_0, T>}::push_unchecked]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 949:4-949:65
    Name pattern: [core::array::{core::array::Guard<'0, @T>}::push_unchecked] -/
@[rust_fun "core::array::{core::array::Guard<'0, @T>}::push_unchecked"]
def core.array.Guard.push_unchecked
  {T : Type} (self : core.array.Guard T) (item : T) :
  Result ((core.array.Guard T) × (core.array.Guard T → core.array.Guard T))
  := do
  let (mu, get_unchecked_mut_back) ←
    core.slice.Slice.get_unchecked_mut (core.slice.index.SliceIndexUsizeSlice
      (core.mem.maybe_uninit.MaybeUninit T)) self.array_mut self.initialized
  let (t, write_back) ← core.mem.maybe_uninit.MaybeUninit.write mu item
  let i ← core.num.Usize.unchecked_add self.initialized 1#usize
  let mu1 := write_back t
  let s := get_unchecked_mut_back mu1
  let back := fun self1 => { self with array_mut := self1.array_mut }
  ok ({ array_mut := s, initialized := i }, back)

end AspisR1CuArraySource

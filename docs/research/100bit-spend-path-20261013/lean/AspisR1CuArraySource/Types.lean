-- Exact selected emitted declaration; body unchanged.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1CuArraySource

-- Explicit initialized/uninitialized primitive interpretation, not a type axiom.
abbrev core.mem.maybe_uninit.MaybeUninit (T : Type) := Option T

/-- [core::array::Guard]
    Source: '/rustc/library/core/src/array/mod.rs', lines 934:0-934:19
    Name pattern: [core::array::Guard] -/
@[rust_type "core::array::Guard" (mutRegions := #[0])]
structure core.array.Guard (T : Type) where
  array_mut : Slice (core.mem.maybe_uninit.MaybeUninit T)
  initialized : Std.Usize

end AspisR1CuArraySource

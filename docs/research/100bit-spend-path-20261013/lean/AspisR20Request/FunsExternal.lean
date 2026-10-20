import AspisR20Request.Types

/-! P6 library interface for std slice/array equality. Rust 1.93 implements
this using `as_array`; the pinned Charon cannot lower its pointer cast. This
model delegates to the existing Aeneas slice/slice comparator after the
array-to-slice coercion. Kani's slice_array_header_comparison_model checks eq
and ne for every four-byte header and every input length 0..320. The codec
only uses this interface for four-byte magic headers. No new axiom. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace Slice.Insts.CoreCmpPartialEqArray

def eq {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
    (s : Slice T) (a : Array U N) : Result Bool :=
  core.slice.cmp.PartialEqSlice.eq cmp s a.to_slice

def ne {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
    (s : Slice T) (a : Array U N) : Result Bool :=
  core.slice.cmp.PartialEqSlice.ne cmp s a.to_slice

#print axioms eq
#print axioms ne
end Slice.Insts.CoreCmpPartialEqArray

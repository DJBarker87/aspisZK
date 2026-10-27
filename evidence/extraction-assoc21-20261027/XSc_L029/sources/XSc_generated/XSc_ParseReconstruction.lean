import XSc_ParseCuts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_ParseReconstruction
def parse (bytes : Slice U8) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 if Slice.len bytes < 32#usize then ok (.Err (.Length 0#u8)) else
 let s ← core.slice.index.Slice.index
  (core.slice.index.SliceIndexRangeToUsizeSlice U8) bytes {«end»:=32#usize}
 let r ← core.array.TryFromSharedArraySlice.try_from 32#usize s
 match r with
 | .Err _ => ok (.Err (.Length 0#u8))
 | .Ok root => XSc_ParseCuts.tail0 bytes root 32#usize
/-- All source cuts reconstruct the actual emitted parser exactly, with no
source-shape, success or validation hypothesis. -/
theorem source (bytes : Slice U8) : r1_wire.Prefix.parse bytes=parse bytes := by
 unfold r1_wire.Prefix.parse parse
 split
 · rfl
 · congr 1
   funext s
   congr 1
   funext root
   cases root <;> rfl
#print axioms source
end XSc_ParseReconstruction

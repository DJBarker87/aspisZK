import XSg_OldStage00
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_OldReconstruction
open XSg_ParseLiteral
/-- Exact source header and the opaque literal suffix. -/
def parse (bytes : Slice U8) : Result (core.result.Result OldPrefix OldError) := do
 if Slice.len bytes<32#usize then ok (.Err (.Length 0#u8)) else
 let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) bytes {«end»:=32#usize}
 let r ← core.array.TryFromSharedArraySlice.try_from 32#usize s
 match r with
 | .Err _ => ok (.Err (.Length 0#u8))
 | .Ok root => XSg_OldCuts.tail0 bytes root 32#usize
/-- The split source reconstructs the complete literal old parser. -/
theorem source (bytes : Slice U8) :
 AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=parse bytes := by rfl
#print axioms source
end XSg_OldReconstruction

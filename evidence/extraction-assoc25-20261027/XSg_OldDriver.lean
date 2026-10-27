import XSg_OldReconstruction
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_OldDriver
open XSg_ParseLiteral
def parse (bytes : Slice U8) : Result (core.result.Result OldPrefix OldError) := do
 if Slice.len bytes<32#usize then ok (.Err (.Length 0#u8)) else
 let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) bytes {«end»:=32#usize}
 let r ← core.array.TryFromSharedArraySlice.try_from 32#usize s
 match r with
 | .Err _ => ok (.Err (.Length 0#u8))
 | .Ok root =>
  let out ← XRx_StageFold.fold (XSe_ParseStages.oldStep bytes) (List.range' 0 27) (.Ok ([],32#usize))
  match out with | .Err e => ok (.Err e) | .Ok s => XSe_ParseFinish.finish bytes root s
/-- Install all27 literal continuations into the SINGLE generic driver law,
retaining every error, state and final prefix field. -/
theorem source (bytes : Slice U8) :
 AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=parse bytes := by
 rw [XSg_OldReconstruction.source]
 unfold XSg_OldReconstruction.parse parse
 split
 · rfl
 · congr 1
   funext s
   congr 1
   funext root
   cases root with
   | Err e => rfl
   | Ok root =>
    rw [XSg_OldStage00.source]
    unfold XSg_OldResume.run
    rw [XRx_TryDriver.source]
    rfl
#print axioms source
end XSg_OldDriver

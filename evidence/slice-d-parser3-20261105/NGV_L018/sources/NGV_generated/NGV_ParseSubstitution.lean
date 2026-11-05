import NGV_Validator
import NGD_ParseReference
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ParseSubstitution
open AspisR1PrefixAggregateParser
/-- Same parser and original borrowed payload; only the child reply changes. -/
theorem congr (row : U8) (record : Slice U8)
 (left right : U8 → Slice U8 → Result (core.result.Result Unit r1_wire.Error))
 (law : ∀ payload, core.slice.index.Slice.index
   (core.slice.index.SliceIndexRangeFromUsizeSlice U8) record {start:=5#usize}=ok payload →
   left row payload=right row payload) :
 NGD_ParseCut.invoke left row record=NGD_ParseCut.invoke right row record := by
 unfold NGD_ParseCut.invoke
 congr 1

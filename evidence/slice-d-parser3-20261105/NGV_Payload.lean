import NGV_Monad
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_Payload
/-- Input-derived borrowed value, including malformed short records. -/
def original (record : Slice U8) : Slice U8 := ⟨record.val.drop 5,by
 have h:=record.property;simp only [List.length_drop];omega⟩
theorem selected (record payload : Slice U8)
 (run : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
   record {start:=5#usize}=ok payload) : payload=original record := by
 simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeFromUsizeSlice,
   core.slice.index.SliceIndexRangeFromUsizeSlice.index] at run
 split at run
 · have same:=Result.ok.inj run
   apply Subtype.ext
   exact congrArg Subtype.val same.symm
 · cases run
#print axioms selected
end NGV_Payload

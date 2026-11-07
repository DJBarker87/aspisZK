import NMP_PrepareState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Source occurrence3: values; complete reply and writeback at SAME arguments. -/
theorem occurrence3 {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack) :
 step c (.values s semantic y1 back vecBack) = (do
   let src ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
     s.bytes {start:=7031#usize,«end»:=7495#usize}
   let (r,after) ← invoke "TX1:099/expand_values" (src,y1) (c.c11 src y1)
   match r with
   | .Err _ => pure (.inl (.Err verifier.Error.Parse,s.scratch))
   | .Ok _ =>
     let logical := vecBack (back (semantic,after))
     let fullSemantic ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
       logical {«end»:=13831#usize}
     let fullY1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
       logical {start:=13831#usize}
     pure (.inr (.view s fullSemantic fullY1))) := rfl
#print axioms occurrence3
end AspisR1.NMP_PrepareSteps

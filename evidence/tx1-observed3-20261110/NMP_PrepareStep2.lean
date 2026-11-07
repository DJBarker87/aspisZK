import NMP_PrepareState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Source occurrence2: semantic; complete reply and writeback at SAME arguments. -/
theorem occurrence2 {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack) :
 step c (.semantic s semantic y1 back vecBack) = (do
   let src ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
     s.bytes {start:=16#usize,«end»:=7031#usize}
   let (r,after) ← invoke "TX1:098/expand_semantic" (src,semantic) (c.c10 src semantic)
   match r with
   | .Err _ => pure (.inl (.Err verifier.Error.Parse,s.scratch))
   | .Ok _ => pure (.inr (.values s after y1 back vecBack))) := rfl
#print axioms occurrence2
end AspisR1.NMP_PrepareSteps

import NMP_PrepareState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Source occurrence1: split; complete reply and writeback at SAME arguments. -/
theorem occurrence1 {H W : Type} (c : Calls) (s : Parent H W) (logical : alloc.vec.Vec U8) :
 step c (.split s logical) = (do
   let (bytes,vecBack) := alloc.vec.Vec.deref_mut logical
   let ((semantic,y1),back) ← invoke "std/split_at_mut" (bytes,13831#usize)
     (core.slice.Slice.split_at_mut bytes 13831#usize)
   pure (.inr (.semantic s semantic y1 back vecBack))) := rfl
#print axioms occurrence1
end AspisR1.NMP_PrepareSteps

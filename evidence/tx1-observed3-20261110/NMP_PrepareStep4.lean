import NMP_PrepareState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Source occurrence4: view; complete reply and writeback at SAME arguments. -/
theorem occurrence4 {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8) :
 step c (.view s semantic y1) = (do
   let r ← invoke "TX1:095/wide_view" (s.bytes,semantic,y1) (c.c2 s.bytes semantic y1)
   match r with
   | .Err e => pure (.inl (.Err e,s.scratch))
   | .Ok v => pure (.inr (.observed s v))) := rfl
#print axioms occurrence4
end AspisR1.NMP_PrepareSteps

import NMP_PrepareState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Source occurrence0: allocate; complete reply and writeback at SAME arguments. -/
theorem occurrence0 {H W : Type} (c : Calls) (s : Parent H W)  :
 step c (.allocate s) = (do
   let r ← invoke "TX1:064/filled" (14759#usize,0#u8) (c.c1 core.marker.CopyU8 14759#usize 0#u8)
   match r with
   | .Err _ => pure (.inl (.Err verifier.Error.Allocation,s.scratch))
   | .Ok logical => pure (.inr (.split s logical))) := rfl
#print axioms occurrence0
end AspisR1.NMP_PrepareSteps

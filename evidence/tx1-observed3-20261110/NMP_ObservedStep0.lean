import NMP_ObservedState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Occurrence 0, parse; exact full typed call, no callee-law premise. -/
theorem occurrence0 {H W : Type} (c : Calls) (s : Parent H W)  :
 step c (.parse s) = (do let r ← invoke "TX1:138/parse" s.bytes (c.c6 s.bytes)
      match r with
      | .Err e => pure (.inl (.Err e))
      | .Ok p => pure (.inr (.mark0 s p))) := rfl
#print axioms occurrence0
end AspisR1.NMP_ObservedSteps

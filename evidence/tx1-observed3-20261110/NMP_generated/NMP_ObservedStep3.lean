import NMP_ObservedState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Occurrence 3, begin_; exact full typed call, no callee-law premise. -/
theorem occurrence3 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
 step c (.begin_ s p t) = (do
      let (r,after) ← invoke "TX1:150/begin" (p,t) (c.c5 s.digest p t)
      match r with
      | .Err e => pure (.inl (.Err e))
      | .Ok ch => pure (.inr (.mark1 s p after ch))) := rfl
#print axioms occurrence3
end AspisR1.NMP_ObservedSteps

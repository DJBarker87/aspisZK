import NMP_ObservedState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Occurrence 1, mark0; exact full typed call, no callee-law premise. -/
theorem occurrence1 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix) :
 step c (.mark0 s p) = (do let _ ← invoke "TX1:130/mark0" (s.observer,0#u8) (c.c8 s.observer 0#u8)
      pure (.inr (.publicTranscript s p))) := rfl
#print axioms occurrence1
end AspisR1.NMP_ObservedSteps

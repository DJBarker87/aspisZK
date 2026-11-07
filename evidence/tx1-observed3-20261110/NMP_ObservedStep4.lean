import NMP_ObservedState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Occurrence 4, mark1; exact full typed call, no callee-law premise. -/
theorem occurrence4 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : aspis_core.state_only_prefix.r0.Challenges) :
 step c (.mark1 s p t ch) = (do
      let _ ← invoke "TX1:130/mark1" (s.observer,1#u8) (c.c8 s.observer 1#u8)
      pure (.inr (.finish s p t ch))) := rfl
#print axioms occurrence4
end AspisR1.NMP_ObservedSteps

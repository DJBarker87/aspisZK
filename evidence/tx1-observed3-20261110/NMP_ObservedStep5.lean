import NMP_ObservedState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Occurrence 5, finish; exact full typed call, no callee-law premise. -/
theorem occurrence5 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : aspis_core.state_only_prefix.r0.Challenges) :
 step c (.finish s p t ch) = (do let r ← invoke "TX1:136/verify_finish" (s.publicValue,p,t,ch,s.observer) (c.c7 s.digest s.publicValue p t ch s.observer)
      pure (.inl r)) := rfl
#print axioms occurrence5
end AspisR1.NMP_ObservedSteps

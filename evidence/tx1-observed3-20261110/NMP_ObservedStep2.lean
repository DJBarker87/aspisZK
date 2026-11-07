import NMP_ObservedState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Occurrence 2, publicTranscript; exact full typed call, no callee-law premise. -/
theorem occurrence2 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix) :
 step c (.publicTranscript s p) = (do let r ← invoke "TX1:131/public_transcript" (s.publicValue,s.hash,p.c1_root) (c.c9 s.digest s.publicValue s.hash p.c1_root)
      match r with
      | .Err e => pure (.inl (.Err e))
      | .Ok t => pure (.inr (.begin_ s p t))) := rfl
#print axioms occurrence2
end AspisR1.NMP_ObservedSteps

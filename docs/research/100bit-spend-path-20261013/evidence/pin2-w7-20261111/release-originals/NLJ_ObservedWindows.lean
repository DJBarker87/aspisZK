import NLJ_ObservedStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
def parseWindow {H : Type} (s : State H) : Code (Post H) := do
 let r ← PrefixAdapter.parseAccepted s.input.bytes
 match r with
 | .Err e => pure (.inl (.Err e))
 | .Ok p => pure (.inr (advance s (.mark0 p)))
def publicWindow {H : Type} (s : State H) (p : r1_wire.Prefix) : Code (Post H) := do
 let r ← S1SemanticCode.publicTranscript s.input.digest s.input.publicValue s.input.hash p.c1_root
 match r with
 | .Err e => pure (.inl (.Err e))
 | .Ok t => pure (.inr (advance s (.begin p t)))
def beginWindow {H : Type} (s : State H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) : Code (Post H) := do
 let (r,after) ← S1SemanticCode.begin s.input.digest p t
 match r with
 | .Err e => pure (.inl (.Err e))
 | .Ok c => pure (.inr (advance s (.mark1 p after c)))
end AspisR1.NLJ_Observed
end

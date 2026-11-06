import NLJ_ObservedState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- SOURCE transcription only. F is the sole OPEN child,136. Native cut
certification is not inferred by this definition or its reduction lemmas. -/
def step {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let F := S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation)
 match s.locals with
 | .parse =>
   let r ← PrefixAdapter.parseAccepted i.bytes
   match r with
   | .Err e => pure (.inl (.Err e))
   | .Ok p => pure (.inr (advance s (.mark0 p)))
 | .mark0 p =>
   VerifyPrefix.mark none 0#u8
   pure (.inr (advance s (.publicTranscript p)))
 | .publicTranscript p =>
   let r ← S1SemanticCode.publicTranscript i.digest i.publicValue i.hash p.c1_root
   match r with
   | .Err e => pure (.inl (.Err e))
   | .Ok t => pure (.inr (advance s (.begin p t)))
 | .begin p t =>
   let (r,after) ← S1SemanticCode.begin i.digest p t
   match r with
   | .Err e => pure (.inl (.Err e))
   | .Ok c => pure (.inr (advance s (.mark1 p after c)))
 | .mark1 p t c =>
   VerifyPrefix.mark none 1#u8
   pure (.inr (advance s (.finish p t c)))
 | .finish p t c =>
   let r ← F i.digest i.publicValue p t c none
   pure (.inl r)
end AspisR1.NLJ_Observed
end

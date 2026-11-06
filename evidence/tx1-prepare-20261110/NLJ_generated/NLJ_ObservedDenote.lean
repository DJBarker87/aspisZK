import NLJ_Monad
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
def rank {H : Type} (s : State H) : Nat :=
 match s.locals with
 | .parse => 6 | .mark0 _ => 5 | .publicTranscript _ => 4
 | .begin _ _ => 3 | .mark1 _ _ _ => 2 | .finish _ _ _ => 1
/-- Exact source continuation, with no native endpoint premise. -/
def denote {H : Type} (s : State H) : Code (Out H) :=
 let F : S1SemanticCode.Finish := S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries s.input.reservation)
 match s.locals with
 | .finish p t c => F s.input.digest s.input.publicValue p t c none
 | .mark1 p t c => do
   VerifyPrefix.mark none 1#u8
   F s.input.digest s.input.publicValue p t c none
 | .begin p t => do
   let (r,after) ← S1SemanticCode.begin s.input.digest p t
   match r with
   | .Err e => pure (.Err e)
   | .Ok c => do
     VerifyPrefix.mark none 1#u8
     F s.input.digest s.input.publicValue p after c none
 | .publicTranscript p => do
   let r ← S1SemanticCode.publicTranscript s.input.digest s.input.publicValue s.input.hash p.c1_root
   match r with
   | .Err e => pure (.Err e)
   | .Ok t => do
     let (r,after) ← S1SemanticCode.begin s.input.digest p t
     match r with
     | .Err e => pure (.Err e)
     | .Ok c => do
       VerifyPrefix.mark none 1#u8
       F s.input.digest s.input.publicValue p after c none
 | .mark0 p => do
   VerifyPrefix.mark none 0#u8
   let r ← S1SemanticCode.publicTranscript s.input.digest s.input.publicValue s.input.hash p.c1_root
   match r with
   | .Err e => pure (.Err e)
   | .Ok t => do
     let (r,after) ← S1SemanticCode.begin s.input.digest p t
     match r with
     | .Err e => pure (.Err e)
     | .Ok c => do
       VerifyPrefix.mark none 1#u8
       F s.input.digest s.input.publicValue p after c none
 | .parse => S1SemanticCode.verify F s.input.digest s.input.publicValue s.input.bytes s.input.hash none
end AspisR1.NLJ_Observed
end

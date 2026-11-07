import NMP_ReachedAlgebra
import NMP_Composition137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Reached137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run Log)
open NMP_Transcription137
def quiet {H : Type} (c : Cuts H) : Cuts H :=
 {c with mark0:=.done (),mark1:=.done ()}
def code {H : Type} (c : Cuts H) := NMP_Transcription137.code (quiet c)
/-- Each law is applied only at the SAME reached arguments, not at arbitrary
invalid Prefix/challenge states. It is value/log support, not a physical packet. -/
structure Agreement {H : Type} (a b : Cuts H) : Prop where
 parse : run a.parse=run b.parse
 publicTranscript : ∀ lp p, run a.parse=(lp,ok (.Ok p)) →
  run (a.publicTranscript p)=run (b.publicTranscript p)
 begin : ∀ lp p lt t, run a.parse=(lp,ok (.Ok p)) →
  run (a.publicTranscript p)=(lt,ok (.Ok t)) → run (a.begin p t)=run (b.begin p t)
 finish : ∀ lp p lt t lb c after, run a.parse=(lp,ok (.Ok p)) →
  run (a.publicTranscript p)=(lt,ok (.Ok t)) →
  run (a.begin p t)=(lb,ok (.Ok c,after)) →
  run (a.finish p after c)=run (b.finish p after c)
theorem fold {H : Type} (a b : Cuts H) (h : Agreement a b) :
 run (code a)=run (code b) := by
 unfold code NMP_Transcription137.code quiet
 apply NMP_ReachedAlgebra.bind _ _ _ _ h.parse
 intro lp p hp
 cases p with
 | Err e => rfl
 | Ok p =>
  change run (PreparedHashCode.bind (a.publicTranscript p) _) =
   run (PreparedHashCode.bind (b.publicTranscript p) _)
  apply NMP_ReachedAlgebra.bind _ _ _ _ (h.publicTranscript lp p hp)
  intro lt t ht
  cases t with
  | Err e => rfl
  | Ok t =>
   apply NMP_ReachedAlgebra.bind _ _ _ _ (h.begin lp p lt t hp ht)
   intro lb reply hb
   rcases reply with ⟨reply,after⟩
   cases reply with
   | Err e => rfl
   | Ok c => exact h.finish lp p lt t lb c after hp ht hb
/-- Deployed None markers are silent; they are still present in the source
transcription and no assertion about a function-pointer value is introduced. -/
theorem source {H : Type} (i : NLJ_Observed.Input H) :
 run (code (atInput i))=run (S1SemanticCode.verify
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation))
  i.digest i.publicValue i.bytes i.hash none) := by
 have h : NMP_Composition137.ValueAgreement (quiet (atInput i)) (atInput i) :=
  ⟨rfl,rfl,(fun _ => rfl),(fun _ _ => rfl),rfl,(fun _ _ _ => rfl)⟩
 exact (NMP_Composition137.fold _ _ h).trans (NMP_Transcription137.source i)
#print axioms fold
#print axioms source
#print fold
end AspisR1.NMP_Reached137
end

import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_claims (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) : Code (Out H) := do
 let r ← (IDa_Deployed.boundaries i.reservation).claims i.prefix1
 match r with
 | .Ok v => fold n {input:=i,next:=.original,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some v}}
 | .Err error => pure (.Err error)
theorem claims_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) :
 run (fold (n+1) {input:=i,next:=.claims,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript}}) = run (window_claims n i l (running) (alpha) (transcript)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_claims
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r <;> rfl
#print axioms claims_head
end AspisR1.NLI_Window
end

import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_mapPublic (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminalReply : core.result.Result Q aspis_core.state_only_prefix.r0.Error) : Code (Out H) := do
 let r ← core.result.Result.map_err (FinishModel.closureFn11 i.digest) terminalReply ()
 match r with
 | .Ok v => fold n {input:=i,next:=.mark3,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminalReply:=some terminalReply, terminal:=some v}}
 | .Err error => pure (.Err error)
theorem mapPublic_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminalReply : core.result.Result Q aspis_core.state_only_prefix.r0.Error) :
 run (fold (n+1) {input:=i,next:=.mapPublic,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminalReply:=some terminalReply}}) = run (window_mapPublic n i l (running) (alpha) (transcript) (claims) (terminalReply)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_mapPublic
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r <;> rfl
#print axioms mapPublic_head
end AspisR1.NLI_Window
end

import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_terminal (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) : Code (Out H) := do
 let r ← (IDa_Deployed.boundaries i.reservation).terminal i.publicValue claims alpha i.challenges
 fold n {input:=i,next:=.mapPublic,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminalReply:=some r}}
theorem terminal_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) :
 run (fold (n+1) {input:=i,next:=.terminal,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims}}) = run (window_terminal n i l (running) (alpha) (transcript) (claims)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_terminal
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 rfl
#print axioms terminal_head
end AspisR1.NLI_Window
end

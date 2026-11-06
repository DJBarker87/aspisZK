import NLI_Suffix_mapPublic
import NLI_MonadNotation
import NLI_Window_terminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_terminal {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) : Code (Out H) := do
 let r ← (IDa_Deployed.boundaries i.reservation).terminal i.publicValue claims alpha i.challenges
 suffix_mapPublic i (running) (alpha) (transcript) (claims) (r)
theorem terminal {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) :
 run (fold 30 {input:=i,next:=.terminal,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims}}) = run (suffix_terminal i (running) (alpha) (transcript) (claims)) := by
 rw [NLI_Window.terminal_head 29]
 unfold NLI_Window.window_terminal suffix_terminal
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact mapPublic i (l) (running) (alpha) (transcript) (claims) (r)
#print axioms terminal
end AspisR1.NLI_Source
end

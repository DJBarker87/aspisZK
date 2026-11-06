import NLI_Suffix_addMask
import NLI_MonadNotation
import NLI_Window_multiply
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_multiply {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) (extra : Words) : Code (Out H) := do
 let product ← (IDa_Deployed.boundaries i.reservation).mul i.challenges.eta terminal
 suffix_addMask i (running) (alpha) (transcript) (claims) (mask) (extra) (product)
theorem multiply {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) (extra : Words) :
 run (fold 20 {input:=i,next:=.multiply,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, mask:=some mask, extra:=some extra}}) = run (suffix_multiply i (running) (alpha) (transcript) (claims) (terminal) (mask) (extra)) := by
 rw [NLI_Window.multiply_head 19]
 unfold NLI_Window.window_multiply suffix_multiply
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro product
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact addMask i ({l with terminal:=some terminal}) (running) (alpha) (transcript) (claims) (mask) (extra) (product)
#print axioms multiply
end AspisR1.NLI_Source
end

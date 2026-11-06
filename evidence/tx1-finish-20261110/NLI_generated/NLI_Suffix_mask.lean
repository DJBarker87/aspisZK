import NLI_Suffix_record25a
import NLI_MonadNotation
import NLI_Window_mask
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_mask {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) (high : High) (blind : Q) : Code (Out H) := do
 let mask ← (IDa_Deployed.boundaries i.reservation).mask low high blind alpha
 suffix_record25a i (running) (alpha) (transcript) (claims) (terminal) (mask)
theorem mask {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) (high : High) (blind : Q) :
 run (fold 23 {input:=i,next:=.mask,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low, high:=some high, blind:=some blind}}) = run (suffix_mask i (running) (alpha) (transcript) (claims) (terminal) (low) (high) (blind)) := by
 rw [NLI_Window.mask_head 22]
 unfold NLI_Window.window_mask suffix_mask
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro mask
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact record25a i ({l with low:=some low, high:=some high, blind:=some blind}) (running) (alpha) (transcript) (claims) (terminal) (mask)
#print axioms mask
end AspisR1.NLI_Source
end

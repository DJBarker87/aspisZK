import NLI_Suffix_terminalGuard
import NLI_MonadNotation
import NLI_Window_addExtra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_addExtra {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (partialValue : Q) (extraCell : Q) : Code (Out H) := do
 let masked ← (IDa_Deployed.boundaries i.reservation).add partialValue extraCell
 suffix_terminalGuard i (running) (alpha) (transcript) (claims) (extra) (masked)
theorem addExtra {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (partialValue : Q) (extraCell : Q) :
 run (fold 17 {input:=i,next:=.addExtra,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, partialValue:=some partialValue, extraCell:=some extraCell}}) = run (suffix_addExtra i (running) (alpha) (transcript) (claims) (extra) (partialValue) (extraCell)) := by
 rw [NLI_Window.addExtra_head 16]
 unfold NLI_Window.window_addExtra suffix_addExtra
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro masked
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact terminalGuard i ({l with partialValue:=some partialValue, extraCell:=some extraCell}) (running) (alpha) (transcript) (claims) (extra) (masked)
#print axioms addExtra
end AspisR1.NLI_Source
end

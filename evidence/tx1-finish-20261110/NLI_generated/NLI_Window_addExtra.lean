import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_addExtra (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (partialValue : Q) (extraCell : Q) : Code (Out H) := do
 let masked ← (IDa_Deployed.boundaries i.reservation).add partialValue extraCell
 fold n {input:=i,next:=.terminalGuard,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, partialValue:=some partialValue, extraCell:=some extraCell, masked:=some masked}}
theorem addExtra_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (partialValue : Q) (extraCell : Q) :
 run (fold (n+1) {input:=i,next:=.addExtra,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, partialValue:=some partialValue, extraCell:=some extraCell}}) = run (window_addExtra n i l (running) (alpha) (transcript) (claims) (extra) (partialValue) (extraCell)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_addExtra
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro masked
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 rfl
#print axioms addExtra_head
end AspisR1.NLI_Window
end

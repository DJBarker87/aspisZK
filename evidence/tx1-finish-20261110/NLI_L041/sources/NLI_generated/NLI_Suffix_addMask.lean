import NLI_Suffix_extra28
import NLI_MonadNotation
import NLI_Window_addMask
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_addMask {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (mask : Q) (extra : Words) (product : Q) : Code (Out H) := do
 let partialValue ← (IDa_Deployed.boundaries i.reservation).add mask product
 suffix_extra28 i (running) (alpha) (transcript) (claims) (extra) (partialValue)
theorem addMask {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (mask : Q) (extra : Words) (product : Q) :
 run (fold 19 {input:=i,next:=.addMask,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, mask:=some mask, extra:=some extra, product:=some product}}) = run (suffix_addMask i (running) (alpha) (transcript) (claims) (mask) (extra) (product)) := by
 rw [NLI_Window.addMask_head 18]
 unfold NLI_Window.window_addMask suffix_addMask
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro partialValue
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact extra28 i ({l with mask:=some mask, product:=some product}) (running) (alpha) (transcript) (claims) (extra) (partialValue)
#print axioms addMask
end AspisR1.NLI_Source
end

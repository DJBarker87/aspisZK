import NLI_Suffix_highArray
import NLI_MonadNotation
import NLI_Window_lowArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_lowArray {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) : Code (Out H) := do
 let low ← (IDa_Deployed.boundaries i.reservation).fromFn 16#usize (FinishModel.closureFn9 i.digest) claims
 suffix_highArray i (running) (alpha) (transcript) (claims) (terminal) (low)
theorem lowArray {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) :
 run (fold 27 {input:=i,next:=.lowArray,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal}}) = run (suffix_lowArray i (running) (alpha) (transcript) (claims) (terminal)) := by
 rw [NLI_Window.lowArray_head 26]
 unfold NLI_Window.window_lowArray suffix_lowArray
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro low
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact highArray i (l) (running) (alpha) (transcript) (claims) (terminal) (low)
#print axioms lowArray
end AspisR1.NLI_Source
end

import NLI_Suffix_blind
import NLI_MonadNotation
import NLI_Window_highArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_highArray {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) : Code (Out H) := do
 let high ← (IDa_Deployed.boundaries i.reservation).fromFn 10#usize (FinishModel.closureFn5 i.digest) claims
 suffix_blind i (running) (alpha) (transcript) (claims) (terminal) (low) (high)
theorem highArray {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) :
 run (fold 26 {input:=i,next:=.highArray,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low}}) = run (suffix_highArray i (running) (alpha) (transcript) (claims) (terminal) (low)) := by
 rw [NLI_Window.highArray_head 25]
 unfold NLI_Window.window_highArray suffix_highArray
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro high
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact blind i (l) (running) (alpha) (transcript) (claims) (terminal) (low) (high)
#print axioms highArray
end AspisR1.NLI_Source
end

import NLI_Suffix_lowArray
import NLI_MonadNotation
import NLI_FoldTicks
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_mark3 {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) : Code (Out H) := do
 VerifyPrefix.mark none 3#u8
 suffix_lowArray i (running) (alpha) (transcript) (claims) (terminal)
theorem mark3 {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) :
 run (fold 28 {input:=i,next:=.mark3,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal}}) = run (suffix_mark3 i (running) (alpha) (transcript) (claims) (terminal)) := by
 rw [NLI_FoldTicks.mark3 27 _ rfl]
 change run (fold 27 {input:=i,next:=.lowArray,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal}}) = _
 exact NLI_Source.lowArray i l running alpha transcript claims terminal
#print axioms mark3
end AspisR1.NLI_Source
end

import NLI_Suffix_claims
import NLI_MonadNotation
import NLI_FoldTicks
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_mark2 {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) : Code (Out H) := do
 VerifyPrefix.mark none 2#u8
 suffix_claims i (running) (alpha) (transcript)
theorem mark2 {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) :
 run (fold 33 {input:=i,next:=.mark2,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript}}) = run (suffix_mark2 i (running) (alpha) (transcript)) := by
 rw [NLI_FoldTicks.mark2 32 _ rfl]
 change run (fold 32 {input:=i,next:=.claims,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript}}) = _
 exact NLI_Source.claims i l running alpha transcript
#print axioms mark2
end AspisR1.NLI_Source
end

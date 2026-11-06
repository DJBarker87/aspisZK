import NLI_Suffix_terminal
import NLI_MonadNotation
import NLI_FoldTicks
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_original {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) : Code (Out H) := do

 suffix_terminal i (running) (alpha) (transcript) (claims)
theorem original {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) :
 run (fold 31 {input:=i,next:=.original,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims}}) = run (suffix_original i (running) (alpha) (transcript) (claims)) := by
 rw [NLI_FoldTicks.original 30 _ rfl]
 change run (fold 30 {input:=i,next:=.terminal,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims}}) = _
 exact terminal i l running alpha transcript claims
#print axioms original
end AspisR1.NLI_Source
end

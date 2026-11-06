import NLI_Suffix_stateBefore
import NLI_MonadNotation
import NLI_FoldPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_mark4 {H : Type} (i : Input H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) : Code (Out H) := do
 VerifyPrefix.mark none 4#u8
 suffix_stateBefore i (alpha) (transcript) (claims) (extra)
theorem mark4 {H : Type} (i : Input H) (l : Locals H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) :
 run (fold 15 {input:=i,next:=.mark4,locals:={l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra}}) = run (suffix_mark4 i (alpha) (transcript) (claims) (extra)) := by
 rw [NLI_FoldPhase.mark4 14 _ rfl]
 change run (fold 14 {input:=i,next:=.stateBefore,locals:={l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra}}) = _
 exact stateBefore i l alpha transcript claims extra
#print axioms mark4
end AspisR1.NLI_Source
end

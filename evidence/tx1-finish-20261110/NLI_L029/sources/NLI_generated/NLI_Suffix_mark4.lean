import NLI_Suffix_stateBefore
import NLI_MonadNotation
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
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold suffix_mark4
 simp only [NLI_Notation.assoc, NLI_Notation.pure_left, NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro ignored
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact stateBefore i ({l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra}) (alpha) (transcript) (claims) (extra)
#print axioms mark4
end AspisR1.NLI_Source
end

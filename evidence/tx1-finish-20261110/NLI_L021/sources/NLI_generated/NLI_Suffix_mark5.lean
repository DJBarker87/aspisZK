import NLI_Suffix_circleGuard
import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_mark5 {H : Type} (i : Input H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (beforeZ1 : Words) (z1 : Point) : Code (Out H) := do
 VerifyPrefix.mark none 5#u8
 suffix_circleGuard i (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (beforeZ1) (z1)
theorem mark5 {H : Type} (i : Input H) (l : Locals H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (beforeZ1 : Words) (z1 : Point) :
 run (fold 7 {input:=i,next:=.mark5,locals:={l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, beforeZ1:=some beforeZ1, z1:=some z1}}) = run (suffix_mark5 i (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (beforeZ1) (z1)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold suffix_mark5
 simp only [NLI_Notation.assoc, NLI_Notation.pure_left, NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro ignored
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact circleGuard i ({l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, beforeZ1:=some beforeZ1, z1:=some z1}) (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (beforeZ1) (z1)
#print axioms mark5
end AspisR1.NLI_Source
end

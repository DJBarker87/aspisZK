import NLI_Suffix_record25b
import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_stateBefore {H : Type} (i : Input H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) : Code (Out H) := do
 let stateBefore ← r1_wire.SemanticTranscript.impl.state i.digest transcript
 suffix_record25b i (alpha) (transcript) (claims) (extra) (stateBefore)
theorem stateBefore {H : Type} (i : Input H) (l : Locals H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) :
 run (fold 14 {input:=i,next:=.stateBefore,locals:={l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra}}) = run (suffix_stateBefore i (alpha) (transcript) (claims) (extra)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold suffix_stateBefore
 simp only [NLI_Notation.assoc, NLI_Notation.pure_left, NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro stateBefore
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact record25b i ({l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore}) (alpha) (transcript) (claims) (extra) (stateBefore)
#print axioms stateBefore
end AspisR1.NLI_Source
end

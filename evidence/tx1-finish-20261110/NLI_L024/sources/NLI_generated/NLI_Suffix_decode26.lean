import NLI_Suffix_record26b
import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_decode26 {H : Type} (i : Input H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (record26 : r1_wire.ValidatedRecord) : Code (Out H) := do
 let r ← NJM_RoundJoin.R.decode 29#usize record26 0#usize
 match r with
 | .Ok v => suffix_record26b i (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (v)
 | .Err error => pure (.Err error)
theorem decode26 {H : Type} (i : Input H) (l : Locals H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (record26 : r1_wire.ValidatedRecord) :
 run (fold 10 {input:=i,next:=.decode26,locals:={l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, record26:=some record26}}) = run (suffix_decode26 i (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (record26)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold suffix_decode26
 simp only [NLI_Notation.assoc, NLI_Notation.pure_left, NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r with
 | Ok v => exact record26b i ({l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, record26:=some record26, beforeZ1:=some v}) (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (v)
 | Err error => rfl
#print axioms decode26
end AspisR1.NLI_Source
end

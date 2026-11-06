import NLI_Suffix_circle0
import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_record25b {H : Type} (i : Input H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) : Code (Out H) := do
 let r ← r1_wire.Prefix.validated_record i.prefix1 25#u8
 match r with
 | .Ok v => suffix_circle0 i (alpha) (transcript) (claims) (v) (extra) (stateBefore)
 | .Err error => pure (.Err error)
theorem record25b {H : Type} (i : Input H) (l : Locals H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) :
 run (fold 13 {input:=i,next:=.record25b,locals:={l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore}}) = run (suffix_record25b i (alpha) (transcript) (claims) (extra) (stateBefore)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold suffix_record25b
 simp only [NLI_Notation.assoc, NLI_Notation.pure_left, NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r with
 | Ok v => exact circle0 i ({l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, record25:=some v}) (alpha) (transcript) (claims) (v) (extra) (stateBefore)
 | Err error => rfl
#print axioms record25b
end AspisR1.NLI_Source
end

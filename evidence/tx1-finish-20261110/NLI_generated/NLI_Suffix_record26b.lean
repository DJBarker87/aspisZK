import NLI_Suffix_circle1
import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_record26b {H : Type} (i : Input H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (beforeZ1 : Words) : Code (Out H) := do
 let r ← r1_wire.Prefix.validated_record i.prefix1 26#u8
 match r with
 | .Ok v => suffix_circle1 i (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (v) (beforeZ1)
 | .Err error => pure (.Err error)
theorem record26b {H : Type} (i : Input H) (l : Locals H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (beforeZ1 : Words) :
 run (fold 9 {input:=i,next:=.record26b,locals:={l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, beforeZ1:=some beforeZ1}}) = run (suffix_record26b i (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (beforeZ1)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold suffix_record26b
 simp only [NLI_Notation.assoc, NLI_Notation.pure_left, NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r with
 | Ok v => exact circle1 i ({l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, beforeZ1:=some beforeZ1, record26:=some v}) (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (v) (beforeZ1)
 | Err error => rfl
#print axioms record26b
end AspisR1.NLI_Source
end

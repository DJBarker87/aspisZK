import NLI_Suffix_mark5
import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_circle1 {H : Type} (i : Input H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (record26 : r1_wire.ValidatedRecord) (beforeZ1 : Words) : Code (Out H) := do
 let (r,t1) ← S1SemanticCode.circleValidated (IDa_Deployed.boundaries i.reservation) i.digest transcript record26
 match r with
 | .Ok v => suffix_mark5 i (alpha) (t1) (claims) (extra) (stateBefore) (z0) (beforeZ1) (v)
 | .Err error => pure (.Err error)
theorem circle1 {H : Type} (i : Input H) (l : Locals H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (record26 : r1_wire.ValidatedRecord) (beforeZ1 : Words) :
 run (fold 8 {input:=i,next:=.circle1,locals:={l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, record26:=some record26, beforeZ1:=some beforeZ1}}) = run (suffix_circle1 i (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (record26) (beforeZ1)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold suffix_circle1
 simp only [NLI_Notation.assoc, NLI_Notation.pure_left, NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 rintro ⟨r,t1⟩
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r with
 | Ok v => exact mark5 i ({l with alpha:=some alpha, transcript:=some t1, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, record26:=some record26, beforeZ1:=some beforeZ1, z1:=some v}) (alpha) (t1) (claims) (extra) (stateBefore) (z0) (beforeZ1) (v)
 | Err error => rfl
#print axioms circle1
end AspisR1.NLI_Source
end

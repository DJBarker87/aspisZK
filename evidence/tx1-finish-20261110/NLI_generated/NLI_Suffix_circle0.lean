import NLI_Suffix_record26a
import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_circle0 {H : Type} (i : Input H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (record25 : r1_wire.ValidatedRecord) (extra : Words) (stateBefore : Array U8 32#usize) : Code (Out H) := do
 let (r,t1) ← S1SemanticCode.circleValidated (IDa_Deployed.boundaries i.reservation) i.digest transcript record25
 match r with
 | .Ok v => suffix_record26a i (alpha) (t1) (claims) (extra) (stateBefore) (v)
 | .Err error => pure (.Err error)
theorem circle0 {H : Type} (i : Input H) (l : Locals H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (record25 : r1_wire.ValidatedRecord) (extra : Words) (stateBefore : Array U8 32#usize) :
 run (fold 12 {input:=i,next:=.circle0,locals:={l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, record25:=some record25, extra:=some extra, stateBefore:=some stateBefore}}) = run (suffix_circle0 i (alpha) (transcript) (claims) (record25) (extra) (stateBefore)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold suffix_circle0
 simp only [NLI_Notation.assoc, NLI_Notation.pure_left, NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 rintro ⟨r,t1⟩
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r with
 | Ok v => exact record26a i ({l with alpha:=some alpha, transcript:=some t1, claims:=some claims, record25:=some record25, extra:=some extra, stateBefore:=some stateBefore, z0:=some v}) (alpha) (t1) (claims) (extra) (stateBefore) (v)
 | Err error => rfl
#print axioms circle0
end AspisR1.NLI_Source
end

import NLI_Suffix_rootCopy
import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_payload2 {H : Type} (i : Input H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (beforeZ1 : Words) (z1 : Point) : Code (Out H) := do
 let r ← FinishModel.payload i.prefix1 2#u8
 match r with
 | .Ok v => suffix_rootCopy i (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (beforeZ1) (z1) (v)
 | .Err error => pure (.Err error)
theorem payload2 {H : Type} (i : Input H) (l : Locals H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (beforeZ1 : Words) (z1 : Point) :
 run (fold 5 {input:=i,next:=.payload2,locals:={l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, beforeZ1:=some beforeZ1, z1:=some z1}}) = run (suffix_payload2 i (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (beforeZ1) (z1)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold suffix_payload2
 simp only [NLI_Notation.assoc, NLI_Notation.pure_left, NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r with
 | Ok v => exact rootCopy_uniform i ({l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, beforeZ1:=some beforeZ1, z1:=some z1, payload:=some v}) (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (beforeZ1) (z1) (v)
 | Err error => rfl
#print axioms payload2
end AspisR1.NLI_Source
end

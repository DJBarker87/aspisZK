import NLI_TailVerified
import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_rootCopy {H : Type} (i : Input H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (beforeZ1 : Words) (z1 : Point) (payload : Slice U8) : Code (Out H) := do
 let r ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload
 let root ← (IDa_Deployed.boundaries i.reservation).unwrapRoot r
 tailVerified i (root) (alpha) (claims) (extra) (beforeZ1) (stateBefore) (z0) (z1) (transcript)
theorem rootCopy_uniform {H : Type} (i : Input H) (l : Locals H) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (stateBefore : Array U8 32#usize) (z0 : Point) (beforeZ1 : Words) (z1 : Point) (payload : Slice U8) :
 run (fold 4 {input:=i,next:=.rootCopy,locals:={l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, beforeZ1:=some beforeZ1, z1:=some z1, payload:=some payload}}) = run (suffix_rootCopy i (alpha) (transcript) (claims) (extra) (stateBefore) (z0) (beforeZ1) (z1) (payload)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold suffix_rootCopy
 simp only [NLI_Notation.assoc, NLI_Notation.pure_left, NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro root
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact verified i ({l with alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, stateBefore:=some stateBefore, z0:=some z0, beforeZ1:=some beforeZ1, z1:=some z1, payload:=some payload, root:=some root}) (root) (alpha) (claims) (extra) (beforeZ1) (stateBefore) (z0) (z1) (transcript)
#print axioms rootCopy_uniform
end AspisR1.NLI_Source
end

import NLI_TailVerified
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def tailRoot {H : Type} (i : Input H) (payload : Slice U8) (alpha : Alpha)
 (claims : Claims) (extra beforeZ1 : Words) (stateBefore : Array U8 32#usize)
 (z0 z1 : Point) (transcript : r1_wire.SemanticTranscript H) : Code (Out H) := do
 let r ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload
 let root ← (IDa_Deployed.boundaries i.reservation).unwrapRoot r
 tailVerified i root alpha claims extra beforeZ1 stateBefore z0 z1 transcript
theorem rootCopy {H : Type} (i : Input H) (l : Locals H)
 (payload : Slice U8) (alpha : Alpha) (claims : Claims) (extra beforeZ1 : Words)
 (stateBefore : Array U8 32#usize) (z0 z1 : Point) (transcript : r1_wire.SemanticTranscript H) :
 run (fold 4 {input:=i,next:=.rootCopy,locals:={l with payload:=some payload,alpha:=some alpha, claims:=some claims,extra:=some extra,beforeZ1:=some beforeZ1,stateBefore:=some stateBefore, z0:=some z0,z1:=some z1,transcript:=some transcript}}) =
 run (tailRoot i payload alpha claims extra beforeZ1 stateBefore z0 z1 transcript) := by
 rw [fold]
 simp only [step,read]
 unfold tailRoot
 simp only [NLI_Monad.bind_assoc]
 apply NLI_RunLaws.bind_congr
 intro r
 apply NLI_RunLaws.bind_congr
 intro root
 exact verified i _ root alpha claims extra beforeZ1 stateBefore z0 z1 transcript
#print axioms rootCopy
end AspisR1.NLI_Source
end

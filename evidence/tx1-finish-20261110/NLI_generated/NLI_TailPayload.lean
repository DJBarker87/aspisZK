import NLI_TailRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def tailPayload {H : Type} (i : Input H) (alpha : Alpha)
 (claims : Claims) (extra beforeZ1 : Words) (stateBefore : Array U8 32#usize)
 (z0 z1 : Point) (transcript : r1_wire.SemanticTranscript H) : Code (Out H) := do
 let r ← FinishModel.payload i.prefix1 2#u8
 match r with
 | .Ok payload => tailRoot i payload alpha claims extra beforeZ1 stateBefore z0 z1 transcript
 | .Err error => pure (.Err error)
theorem payload2 {H : Type} (i : Input H) (l : Locals H)
 (alpha : Alpha) (claims : Claims) (extra beforeZ1 : Words)
 (stateBefore : Array U8 32#usize) (z0 z1 : Point) (transcript : r1_wire.SemanticTranscript H) :
 run (fold 5 {input:=i,next:=.payload2,locals:={l with alpha:=some alpha, claims:=some claims, extra:=some extra, beforeZ1:=some beforeZ1, stateBefore:=some stateBefore, z0:=some z0, z1:=some z1, transcript:=some transcript}}) =
 run (tailPayload i alpha claims extra beforeZ1 stateBefore z0 z1 transcript) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold tailPayload
 try simp only [NLI_Monad.bind_assoc]
 apply NLI_RunLaws.bind_congr
 intro r
 cases r with
 | Ok payload => exact rootCopy i _ payload alpha claims extra beforeZ1 stateBefore z0 z1 transcript
 | Err error => rfl
#print axioms payload2
end AspisR1.NLI_Source
end

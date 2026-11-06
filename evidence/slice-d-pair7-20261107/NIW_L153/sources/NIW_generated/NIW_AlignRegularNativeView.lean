import NIW_AlignRegularPostBoundary
import NIW_AlignFrames
import NIW_AlignGuardNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularNativeView
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

structure View where
 stream : NIW_AlignFrames.Stream
 scratch : Scratch
 parts : Parts
 reply : Reply Unit

def returning (c : Context) (reply : RU) (after : Scratch) (parts : Parts) : View :=
 let base : NIW_AlignBoundary.Log :=
  ⟨NIT_ErrorTransport.unitReply reply,.Err .Parse,.Err .Parse,after,parts,
   Array.repeat 16#usize NHX_FilledZero.zeroQ,parts,NHX_FilledZero.zeroQ,
   NHI_Scalar.zero,NHI_Scalar.zero,c.partsAddress,id,1⟩
 ⟨⟨base,Array.repeat 16#usize NHX_FilledZero.zeroQ,parts,Array.repeat 4#usize NHI_Scalar.zero⟩,
  after,parts,NIT_ErrorTransport.unitReply reply⟩

/-- Returning regular-error or unshared boundary projection of the actual
collected source reply. Shared success is deliberately left to its separate
Common/partials/high projection; no dummy shared observations are invented. -/
def project (c : Context) (before : Scratch) : Option View :=
 match (NIW_AlignRegularPhase.run c before).2.outcome with
 | fail _ => none
 | div => none
 | ok (.Err err,after,parts) => some (returning c (.Err err) after parts)
 | ok (.Ok (),after,parts) => if NGM_GuardExact.guard c.w.value 2#usize then none
   else some (returning c (.Ok ()) after parts)

/-- Exact source snapshot-to-native-window compatibility. This is a supporting
projection theorem, not a claim that arbitrary supplied raw logs equal it. -/
theorem local_cut (c : Context) (shared : Bool) (reply : RU) (after : Scratch) (parts : Parts)
 (inv : NHX_RegularPost.Inv after parts)
 (terminal : shared=false ∨ ∃ err,reply=.Err err) :
 let view:=returning c reply after parts
 NIW_AlignFrames.cutStream shared c.partsAddress view.stream view.scratch view.parts view.reply := by
 have cp : canonical parts := inv.2.2
 have len : (alloc.vec.Vec.deref after).val.length=64 := inv.2.1
 dsimp only
 rcases terminal with unshared|⟨err,rejected⟩
 · subst shared
   cases reply with
   | Err err =>
    intro i hi slot hs power hp
    simp [NIW_AlignFrames.cutStream,NIW_AlignFrames.window,NIW_AlignBoundary.cut,returning,NIW_AlignBoundary.enteredPartial,NIW_AlignBoundary.enteredHigh,NIW_AlignBoundary.expected,NIT_ErrorTransport.unitReply,hi,hs,hp,cp,len]
   | Ok unit =>
    cases unit
    intro i hi slot hs power hp
    simp [NIW_AlignFrames.cutStream,NIW_AlignFrames.window,NIW_AlignBoundary.cut,returning,NIW_AlignBoundary.enteredPartial,NIW_AlignBoundary.enteredHigh,NIW_AlignBoundary.expected,NIT_ErrorTransport.unitReply,hi,hs,hp,cp,len]
 · subst reply
   intro i hi slot hs power hp
   simp [NIW_AlignFrames.cutStream,NIW_AlignFrames.window,NIW_AlignBoundary.cut,returning,NIW_AlignBoundary.enteredPartial,NIW_AlignBoundary.enteredHigh,NIW_AlignBoundary.expected,NIT_ErrorTransport.unitReply,hi,hs,hp,cp,len]
#print axioms local_cut
end AspisR1.NIW_AlignRegularNativeView

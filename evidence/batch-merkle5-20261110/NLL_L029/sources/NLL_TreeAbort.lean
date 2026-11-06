import NLL_EntryStep
import NLL_AbortHistory
set_option autoImplicit false
noncomputable section
namespace NLL_TreeAbort
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem source (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (root : NLL.Root) (batch kind : Usize)
 (hb : batch.val<2) (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (idx : NLL.Indices) (val : NLL.Values) (events : List Event) (pending : Pending)
 (native : AbortInvocation H proof raw root batch kind idx val events pending) :
 NLL_Prefix.At (NKV_QueryPlan.plan H p (Port4B_KeyInstall.queries raw) batch.val kind.val
   (nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)) root
   (NJV_EntryABI.initial idx val 0#usize)) (leafHistory kind events++pending.answered) pending.parts := by
 obtain ⟨length,stream,entry⟩:=NLL_EntryStep.source H proof raw root batch kind hb hk canonical idx val
 have positive:=NKB_KeyStream.positive batch.val
 have low : (NKB_KeyStream.lo batch.val).val=(if batch.val=0 then 0 else 10) := by
   unfold NKB_KeyStream.lo
   split <;> scalar_tac
 have slot:=(NKV_BatchGeometry.slot batch kind hb hk).1
 rcases native with ⟨rest,rfl,loop⟩
 have span : (0#usize).val+(OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch.val kind.val).length=
     (NKB_KeyStream.count batch.val).val := by rw [length];change 0+_= _;omega
 have room : (NJV_EntryABI.initial idx val 0#usize).n.val+
     (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch.val kind.val).length≤16 := by
   rw [length];change 0+_≤16;omega
 have history:=NLL_AbortHistory.source H proof len p wire (Port4B_KeyInstall.queries raw) batch.val kind
   (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val) _ root hb hk slot low (by omega)
   _ ⟨_,NJV_EntryABI.initial idx val 0#usize,0#usize⟩ (fun _ mem=>mem) span room stream rest pending loop
 have plans : NKV_QueryPlan.plan H p (Port4B_KeyInstall.queries raw) batch.val kind.val
     (nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)) root
     (NJV_EntryABI.initial idx val 0#usize)=
   NLL_LoopHistory.expected H p (Port4B_KeyInstall.queries raw) batch.val kind
     (nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)) root
     (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch.val kind.val)
     (NJV_EntryABI.initial idx val 0#usize) := by
   unfold NKV_QueryPlan.plan NLL_LoopHistory.expected
   have reset : MultiproofConeSlotState.reset (NJV_EntryABI.initial idx val 0#usize)=NJV_EntryABI.initial idx val 0#usize := rfl
   rw [reset]
 rw [plans]
 exact history

set_option pp.proofs false
#print source
#print axioms source
end NLL_TreeAbort
end

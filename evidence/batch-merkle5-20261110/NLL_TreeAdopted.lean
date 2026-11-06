import NLL_TreeReturning
import NLL_TreeAbort
set_option autoImplicit false
noncomputable section
namespace NLL_TreeAdopted
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem returning (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (root : NLL.Root) (batch kind : Usize)
 (hb : batch.val<2) (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot p kind.val))
 (idx : NLL.Indices) (val : NLL.Values) (events : List Event) (out : NLL.Answer)
 (native : NLL.Invocation H proof raw root batch kind idx val events out) :
 let model:=eval H (MultiproofConeSlotState.slotState p (Port4B_KeyInstall.queries raw) batch.val kind.val
   (nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind))
   (NJV_EntryABI.initial idx val 0#usize))
 (leafHistory kind events,NKV_ReturnBoundary.reject (ok out))=(model.1,NKV_TailModel.model model.2) := by
 obtain ⟨nodes,read,observed⟩:=NKV_TreeModel.source H proof len p wire raw root batch kind hb hk canonical rootValue idx val
 have selected : nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)=nodes := by
   unfold nodeView;rw [read]
 have domain:=NLL_TerminalDomain.source H proof len p wire batch.val kind _ hb hk
   (NKV_BatchGeometry.slot batch kind hb hk).1 0
 have width : nodes.val.length=32*OraclePortSelectedDraft.capacity (3*batch.val+kind.val) := by
   rw [selected] at domain;exact domain.2.1
 have packet:=NLL_TreeReturning.source H proof len p wire raw root batch kind hb hk canonical idx val events out native
 rw [packet.1] at observed
 dsimp only
 rw [selected]
 apply Prod.ext
 · rw [packet.2,selected]
   exact (NKV_QueryPlan.slot_history H p (Port4B_KeyInstall.queries raw) batch.val kind.val nodes width root rootValue
     (NJV_EntryABI.initial idx val 0#usize)).symm
 · exact observed

set_option pp.proofs false
#print returning
#print axioms returning
end NLL_TreeAdopted
end

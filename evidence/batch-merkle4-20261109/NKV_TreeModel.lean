import NKV_TailLoop
import NKV_TreeTotal
import NKV_LeafSlot
set_option autoImplicit false
noncomputable section
namespace NKV_TreeModel
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef
open NKV_StepErasure NKV_LoopTransport NKV_ReturnBoundary
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
abbrev HashState := AspisV8R19.SourceDuplexStep.State

theorem source (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (root : Array U8 32#usize) (batch kind : Usize)
 (hb : batch.val<2) (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot p kind.val))
 (idx : Indices) (val : Values) :
 ∃ nodes,(NKV_ConcreteChildren.ops H).op3 proof
     (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)=ok nodes ∧
 reject (NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof raw root batch kind idx val ())=
 NKV_TailModel.model (eval H (MultiproofConeSlotState.slotState p (Port4B_KeyInstall.queries raw)
   batch.val kind.val nodes (NJV_EntryABI.initial idx val 0#usize))).2 := by
 obtain ⟨keys,entry⟩:=NKV_TreeBuild.source H proof len p wire raw root batch kind hb hk canonical idx val
 let initial:=NJV_EntryABI.initial idx val 0#usize
 have slot:=(NKV_BatchGeometry.slot batch kind hb hk).1
 obtain ⟨nodes,nodeRead,width,bytes⟩:=NKV_SlotInvocation.physical H proof len p wire batch.val kind.val hb hk _ slot
 refine ⟨nodes,nodeRead,?_⟩
 have room : initial.n.val+(OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch.val kind.val).length≤16 := by
   have length:=MultiproofConeLeafFrozen.sorted_length (Port4B_KeyInstall.queries raw) batch.val kind.val
   change 0+_≤16;omega
 obtain ⟨answer,run⟩:=NKV_LeafTotal.source H p (Port4B_KeyInstall.queries raw) kind.val _ initial room
 rcases answer with ⟨keep,after⟩
 have reset : MultiproofConeSlotState.reset initial=initial := rfl
 rw [NKV_LeafSlot.source]
 dsimp only
 rw [show MultiproofConeSlotState.reset (NJV_EntryABI.initial idx val 0#usize)=initial from reset,run]
 cases keep with
 | false =>
   rw [run] at entry
   rw [entry]
   rfl
 | true =>
   have domain:=NKV_ProducerDomain.caller H p (Port4B_KeyInstall.queries raw) batch.val kind.val initial after rfl run
   obtain ⟨same,read,tail⟩:=NKV_TailLoop.source H proof len p wire root batch.val kind
     (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
     (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind) rootValue hb hk slot keys after (by omega)
   have eq : same=nodes := Result.ok.inj (read.symm.trans nodeRead)
   subst same
   rw [run] at entry
   rw [entry]
   exact tail

set_option pp.proofs false
#print source
#print axioms source
end NKV_TreeModel
end

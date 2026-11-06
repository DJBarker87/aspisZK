import NKV_TreeBuild
import NKV_LeafTotal
import NKV_TailTotal
import NKV_ProducerDomain
set_option autoImplicit false
noncomputable section
namespace NKV_TreeTotal
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef
open NKV_StepErasure NKV_LoopTransport NKV_ReturnBoundary
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

theorem source (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (root : Array U8 32#usize) (batch kind : Usize)
 (hb : batch.val<2) (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (idx : Indices) (val : Values) :
 ∃ r i v,NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof raw root batch kind idx val ()=ok (r,i,v) := by
 obtain ⟨keys,entry⟩:=NKV_TreeBuild.source H proof len p wire raw root batch kind hb hk canonical idx val
 let initial:=NJV_EntryABI.initial idx val 0#usize
 have room : initial.n.val+(OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch.val kind.val).length≤16 := by
   have length:=MultiproofConeLeafFrozen.sorted_length (Port4B_KeyInstall.queries raw) batch.val kind.val
   change 0+_≤16;omega
 obtain ⟨answer,run⟩:=NKV_LeafTotal.source H p (Port4B_KeyInstall.queries raw) kind.val _ initial room
 rcases answer with ⟨keep,after⟩
 cases keep with
 | false =>
   rw [run] at entry
   exact ⟨.Err .Merkle,after.idx,after.val,entry⟩
 | true =>
   have domain:=NKV_ProducerDomain.caller H p (Port4B_KeyInstall.queries raw) batch.val kind.val initial after rfl run
   have slot:=(NKV_BatchGeometry.slot batch kind hb hk).1
   obtain ⟨out,tail⟩:=NKV_TailTotal.loop H proof len p wire root batch.val kind (NKB_KeyStream.lo batch.val)
     (NKB_KeyStream.count batch.val) (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)
     hb hk slot keys after (by omega)
   rw [run] at entry
   change _=(NKV_FRef.verifier.candidate.batch_tree_loop (NKV_ConcreteChildren.ops H)
     (NKV_ConcreteChildren.digest H) proof root kind after.idx after.val ()
     (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
     (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind) keys after.n (NKB_KeyStream.count batch.val) >>= returned) at entry
   rw [tail] at entry
   exact ⟨out.2.2.1,out.1,out.2.1,entry⟩

set_option pp.proofs false
#print source
#print axioms source
end NKV_TreeTotal
end

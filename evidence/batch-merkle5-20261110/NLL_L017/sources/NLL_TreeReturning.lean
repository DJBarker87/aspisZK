import NLL_EntryStep
import NLL_LoopValue
import NLL_LoopHistory
set_option autoImplicit false
noncomputable section
namespace NLL_TreeReturning
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Complete returning native invocation association, on the explicit local
carrier domain. This is NOT yet an (aq)(2) row root: headline carrier
installation and runtime abort prefixes are separate obligations. No child
success, whole endpoint, arbitrary stream, or Ops dictionary is assumed. -/
theorem source (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (root : NLL.Root) (batch kind : Usize)
 (hb : batch.val<2) (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (idx : NLL.Indices) (val : NLL.Values) (events : List Event) (out : NLL.Answer)
 (native : Invocation H proof raw root batch kind idx val events out) :
 NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
   proof raw root batch kind idx val ()=ok out ∧
 leafHistory kind events=NKV_QueryPlan.plan H p (Port4B_KeyInstall.queries raw) batch.val kind.val
   (nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)) root
   (NJV_EntryABI.initial idx val 0#usize) := by
 obtain ⟨length,stream,entry⟩:=NLL_EntryStep.source H proof raw root batch kind hb hk canonical idx val
 have positive:=NKB_KeyStream.positive batch.val
 have low : (NKB_KeyStream.lo batch.val).val=(if batch.val=0 then 0 else 10) := by
   unfold NKB_KeyStream.lo
   split <;> scalar_tac
 have slot:=(NKV_BatchGeometry.slot batch kind hb hk).1
 rcases native with ⟨rest,rfl,loop⟩
 have span : (0#usize).val+(OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch.val kind.val).length=
     (NKB_KeyStream.count batch.val).val := by rw [length];rfl
 have room : (NJV_EntryABI.initial idx val 0#usize).n.val+
     (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch.val kind.val).length≤16 := by
   rw [length];change 0+_≤16;omega
 have value:=NLL_LoopValue.source H proof len p wire (Port4B_KeyInstall.queries raw) batch.val kind
   (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val) _ root hb hk slot low (by omega)
   _ ⟨_,NJV_EntryABI.initial idx val 0#usize,0#usize⟩ (fun _ mem=>mem) span room stream rest out loop
 have history:=NLL_LoopHistory.source H proof len p wire (Port4B_KeyInstall.queries raw) batch.val kind
   (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val) _ root hb hk slot low (by omega)
   _ ⟨_,NJV_EntryABI.initial idx val 0#usize,0#usize⟩ (fun _ mem=>mem) span room stream rest out loop
 constructor
 · exact entry.trans value
 · simpa only [leafHistory,List.flatMap_cons,List.nil_append,NKV_QueryPlan.plan,NLL_LoopHistory.expected,
     MultiproofConeSlotState.reset,NJV_EntryABI.initial] using history

set_option pp.proofs false
#print source
#print axioms source
end NLL_TreeReturning
end

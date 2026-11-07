import NNC_C04Events
set_option autoImplicit false
noncomputable section
namespace NNC_C04StopEvents
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 MultiproofConeRef NLL NLL_Parent NNC_C04Events
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The native stopped child's answered requests keep their original parts;
its pending syscall stays a separate request with NO invented reply/suffix. -/
inductive PendingTrace (H : Bytes → State) (proof : Slice U8) (root : Root)
 (batch : Nat) (kind lo n slot : Usize) : Frame → List NLL.Event → Pending → SdkC_Source.Log → Prop where
 | leaf (f : Frame) (more : f.position<n) :
   PendingTrace H proof root batch kind lo n slot f []
     ⟨Port4B_LeafCode.input kind (view H proof lo (key f)),[],advance f f.scratch,f.scratch⟩ []
 | verify (f : Frame) (done : ¬f.position<n)
   (well : OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys f.scratch))
   (fits : OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys f.scratch)≤OraclePortSelectedDraft.capacity (3*batch+kind.val))
   (padding : MultiproofConePadding.scan
     (4*(OraclePortSelectedDraft.capacity (3*batch+kind.val)-OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys f.scratch)))
     ((MultiproofConeCanonical.bytesOf (nodeView H proof slot).val).drop
       (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys f.scratch)))=true)
   (queries : List (NJP_RowModel.Request × NJP_RowModel.Digest))
   (q : NJP_RowModel.Request) (pending : NJP_RowModel.Scratch)
   (child : NJV_AbortEntry.Invocation (NJP_RequestTransport.hash (MultiproofConePhysicalTransport.rawOracle H)) root
     (MultiproofConeSlotTail.prefixNodes (nodeView H proof slot) (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys f.scratch)))
     (NJV_EntryABI.initial f.scratch.idx f.scratch.val f.scratch.n) queries q pending) :
   PendingTrace H proof root batch kind lo n slot f []
     ⟨NJP_RequestTransport.address q,NJV_AdoptedObservation.history queries,f,NJP_ScratchCarrier.emitted pending⟩ (nodes queries)
 | next (f : Frame) (t : reference.Scratch) (more : f.position<n)
   (step : reference.leaf_step f.scratch (Port4B_NativeLeaf.decodedIndex (key f))
     (digest H proof kind lo f)=ok (some t)) (events : List NLL.Event) (pending : Pending) (trace : SdkC_Source.Log)
   (tail : PendingTrace H proof root batch kind lo n slot (advance f t) events pending trace) :
   PendingTrace H proof root batch kind lo n slot f (event H proof kind lo f::events) pending trace


theorem pending_source {H : Bytes → State} {proof : Slice U8} {root : Root}
 {batch : Nat} {kind lo n slot : Usize} {f : Frame} {events : List NLL.Event} {pending : Pending}
 (native : NLL.AbortLoop H proof root batch kind lo n slot f events pending) :
 ∃ trace, PendingTrace H proof root batch kind lo n slot f events pending trace := by
 induction native with
 | leaf f more => exact ⟨[],.leaf f more⟩
 | verify f done well fits padding queries q scratch child =>
   exact ⟨nodes queries,.verify f done well fits padding queries q scratch child⟩
 | next f t more step events pending tail ih =>
   obtain ⟨trace,ih⟩ := ih
   exact ⟨trace,.next f t more step events pending trace ih⟩

theorem pending_read {H : Bytes → State} {proof : Slice U8} {root : Root}
 {batch : Nat} {kind lo n slot : Usize} {f : Frame} {events : List NLL.Event} {pending : Pending}
 {trace : SdkC_Source.Log}
 (native : PendingTrace H proof root batch kind lo n slot f events pending trace) :
 SdkC_Source.readLog trace = pending.answered := by
 induction native with
 | leaf => rfl
 | verify => exact nodes_read _
 | next f t more step events pending trace tail ih => exact ih

def TreeStopped (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (root : Root) (batch kind : Usize) (idx : Indices) (val : Values)
 (events : List NLL.Event) (pending : Pending) (trace : SdkC_Source.Log) : Prop :=
 ∃ rest,events=.entry (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
   (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind) (entryKeys H raw batch.val kind)::rest ∧
 PendingTrace H proof root batch.val kind (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
   (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)
   ⟨entryKeys H raw batch.val kind,NJV_EntryABI.initial idx val 0#usize,0#usize⟩ rest pending trace

theorem tree_source {H : Bytes → State} {proof : Slice U8} {raw : Array U32 22#usize}
 {root : Root} {batch kind : Usize} {idx : Indices} {val : Values}
 {events : List NLL.Event} {pending : Pending}
 (native : AbortInvocation H proof raw root batch kind idx val events pending) :
 ∃ trace, TreeStopped H proof raw root batch kind idx val events pending trace := by
 obtain ⟨rest,events,tail⟩ := native
 obtain ⟨trace,rendered⟩ := pending_source tail
 exact ⟨trace,rest,events,rendered⟩

inductive Stopped (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize) (batch : Usize) :
 List Call → NLL.Indices → NLL.Values → NLL.History → Pending → SdkC_Source.Log → Prop where
 | here (root : Root) (kind : Usize) (rest : List Call) (idx : Indices) (val : Values)
   (events : List NLL.Event) (pending : Pending) (trace : SdkC_Source.Log)
   (child : TreeStopped H proof raw root batch kind idx val events pending trace) :
   Stopped H proof raw batch ((root,kind)::rest) idx val (leafHistory kind events) pending (tree kind events++trace)
 | next (root : Root) (kind : Usize) (rest : List Call) (idx nextIdx : Indices) (val nextVal : Values)
   (events : List NLL.Event) (history : NLL.History) (pending : Pending) (trace : SdkC_Source.Log)
   (child : NLL.Invocation H proof raw root batch kind idx val events (.Ok (),nextIdx,nextVal))
   (tail : Stopped H proof raw batch rest nextIdx nextVal history pending trace) :
   Stopped H proof raw batch ((root,kind)::rest) idx val (leafHistory kind events++history) pending
    (tree kind events++trace)

theorem stopped_source {H : Bytes → State} {proof : Slice U8} {raw : Array U32 22#usize} {batch : Usize}
 {calls : List Call} {idx : Indices} {val : Values} {history : NLL.History} {pending : Pending}
 (native : AbortCalls H proof raw batch calls idx val history pending) :
 ∃ trace, Stopped H proof raw batch calls idx val history pending trace := by
 induction native with
 | here root kind rest idx val events pending child =>
   obtain ⟨trace,child⟩ := tree_source child
   exact ⟨tree kind events++trace,.here root kind rest idx val events pending trace child⟩
 | next root kind rest idx nextIdx val nextVal events history pending child tail ih =>
   obtain ⟨trace,ih⟩ := ih
   exact ⟨tree kind events++trace,.next root kind rest idx nextIdx val nextVal events history pending trace child ih⟩

theorem stopped_read {H : Bytes → State} {proof : Slice U8} {raw : Array U32 22#usize} {batch : Usize}
 {calls : List Call} {idx : Indices} {val : Values} {history : NLL.History} {pending : Pending}
 {trace : SdkC_Source.Log} (native : Stopped H proof raw batch calls idx val history pending trace) :
 SdkC_Source.readLog trace = history ++ pending.answered := by
 induction native with
 | here root kind rest idx val events pending trace child =>
   obtain ⟨rest,_,child⟩ := child
   rw [read_append,tree_read,pending_read child]
 | next root kind rest idx nextIdx val nextVal events history pending trace child tail ih =>
   rw [read_append,tree_read,ih,List.append_assoc]

#print axioms pending_source
#print axioms pending_read
#print axioms tree_source
#print axioms stopped_source
#print axioms stopped_read
end NNC_C04StopEvents

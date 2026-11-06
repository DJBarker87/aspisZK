import NLL_TreeAdopted
import NLL_AdoptedAbort
import NLL_TreeDomains
import NLL_AbortDomains
set_option autoImplicit false
noncomputable section
namespace NLN
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-- Universal law of the retained reviewed native fold. Invocation is in the
conclusion, never a successful child or endpoint input to a row root. -/
structure TreePacket (H : Bytes → State) (proof : Slice U8)
 (p : OraclePortCompactDraft.Parsed) (raw : Array U32 22#usize)
 (root : NLL.Root) (batch kind : Usize) : Prop where
 returning : ∀ (idx : NLL.Indices) (val : NLL.Values) (events : List Event) (out : NLL.Answer),
   NLL.Invocation H proof raw root batch kind idx val events out →
   NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
     proof raw root batch kind idx val ()=ok out ∧
   leafHistory kind events=NKV_QueryPlan.plan H p (Port4B_KeyInstall.queries raw) batch.val kind.val
     (nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)) root
     (NJV_EntryABI.initial idx val 0#usize) ∧
   (leafHistory kind events,NKV_ReturnBoundary.reject (ok out))=
     NLL_ObservedCalls.tree H proof p raw batch kind idx val
 aborting : ∀ (idx : NLL.Indices) (val : NLL.Values) (events : List Event) (pending : Pending),
   AbortInvocation H proof raw root batch kind idx val events pending →
   NLL_Prefix.At (NKV_QueryPlan.plan H p (Port4B_KeyInstall.queries raw) batch.val kind.val
     (nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)) root
     (NJV_EntryABI.initial idx val 0#usize)) (leafHistory kind events++pending.answered) pending.parts ∧
   NLL_Prefix.At (NLL_ObservedCalls.tree H proof p raw batch kind idx val).1
     (leafHistory kind events++pending.answered) pending.parts
 counts : ∀ (idx : NLL.Indices) (val : NLL.Values) (events : List Event) (out : NLL.Answer),
   NLL.Invocation H proof raw root batch kind idx val events out →
   ∀ (nodes : Slice U8) (count : Nat) (before : reference.Scratch)
     (queries : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (answer : Bool × NJP_RowModel.Scratch),
   Event.verify nodes count before queries answer∈events →
   0<before.n.val ∧ before.n.val≤(if batch.val=0 then 10 else 12) ∧
     OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys before)
 abortCount : ∀ (idx : NLL.Indices) (val : NLL.Values) (events : List Event) (pending : Pending),
   AbortInvocation H proof raw root batch kind idx val events pending →
   pending.parent.scratch.n.val≤(if batch.val=0 then 10 else 12)
 bytes : ∀ count : Nat,
   (MultiproofConeSlotTail.prefixNodes
     (nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)) count).val.length≤9216

theorem tree (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (root : NLL.Root) (batch kind : Usize)
 (hb : batch.val<2) (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot p kind.val)) :
 TreePacket H proof p raw root batch kind := by
 constructor
 · intro idx val events out native
   obtain ⟨value,history⟩:=NLL_TreeReturning.source H proof len p wire raw root batch kind hb hk canonical idx val events out native
   exact ⟨value,history,NLL_TreeAdopted.returning H proof len p wire raw root batch kind hb hk canonical rootValue idx val events out native⟩
 · intro idx val events pending native
   exact ⟨NLL_TreeAbort.source H proof len p wire raw root batch kind hb hk canonical idx val events pending native,
     NLL_AdoptedAbort.tree H proof len p wire raw root batch kind hb hk canonical rootValue idx val events pending native⟩
 · exact NLL_TreeDomains.source H proof raw root batch kind
 · exact NLL_AbortDomains.source H proof raw root batch kind
 · intro count
   exact (NLL_TerminalDomain.source H proof len p wire batch.val kind _ hb hk
     (NKV_BatchGeometry.slot batch kind hb hk).1 count).2.2

set_option pp.proofs false
#print TreePacket
#print tree
#print axioms tree
end NLN
end

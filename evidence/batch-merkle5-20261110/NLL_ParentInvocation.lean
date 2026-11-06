import NLL_TreeReturning
import NKV_ParentSource
set_option autoImplicit false
noncomputable section
namespace NLL_Parent
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Call := NLL.Root × Usize
abbrev Roots := Array NLL.Root 3#usize

def sites (roots : Roots) : List Call :=
 [(Port3_NativeBatchCalls.rootAt roots 0,0#usize),
  (Port3_NativeBatchCalls.rootAt roots 1,1#usize),
  (Port3_NativeBatchCalls.rootAt roots 2,2#usize)]

/-- Actual parent cut K022–K024: both full arrays thread to each later call;
the first Rust Err has no continuation field. Child calls are real SAME
Invocation packets, never arbitrary replies or a three-true assumption. -/
inductive Calls (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize) (batch : Usize) :
 List Call → NLL.Indices → NLL.Values → NLL.History → NLL.Reply → Prop where
 | nil (idx : NLL.Indices) (val : NLL.Values) : Calls H proof raw batch [] idx val [] (.Ok ())
 | error (root : NLL.Root) (kind : Usize) (rest : List Call) (idx nextIdx : NLL.Indices) (val nextVal : NLL.Values)
   (events : List Event) (error : verifier.Error)
   (child : Invocation H proof raw root batch kind idx val events (.Err error,nextIdx,nextVal)) :
   Calls H proof raw batch ((root,kind)::rest) idx val (leafHistory kind events) (.Err error)
 | next (root : NLL.Root) (kind : Usize) (rest : List Call) (idx nextIdx : NLL.Indices) (val nextVal : NLL.Values)
   (events : List Event) (tailHistory : NLL.History) (out : NLL.Reply)
   (child : Invocation H proof raw root batch kind idx val events (.Ok (),nextIdx,nextVal))
   (tail : Calls H proof raw batch rest nextIdx nextVal tailHistory out) :
   Calls H proof raw batch ((root,kind)::rest) idx val (leafHistory kind events++tailHistory) out

def model (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize) (batch : Usize) :
 List Call → NLL.Indices → NLL.Values → Result NLL.Reply
 | [],_,_ => ok (.Ok ())
 | (root,kind)::rest,idx,val =>
   NKV_ParentSource.next (NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
     (NKV_ConcreteChildren.digest H) proof raw root batch kind idx val ())
     (fun i v => model H proof raw batch rest i v)

def plan (H : Bytes → State) (proof : Slice U8) (p : OraclePortCompactDraft.Parsed)
 (raw : Array U32 22#usize) (batch : Usize) : List Call → NLL.Indices → NLL.Values → NLL.History
 | [],_,_ => []
 | (root,kind)::rest,idx,val =>
   let first:=NKV_QueryPlan.plan H p (Port4B_KeyInstall.queries raw) batch.val kind.val
     (nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)) root
     (NJV_EntryABI.initial idx val 0#usize)
   first++match NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
     (NKV_ConcreteChildren.digest H) proof raw root batch kind idx val () with
     | .ok (.Ok _,i,v) => plan H proof p raw batch rest i v
     | _ => []

def Invocation (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (roots : Roots) (batch : Usize) (history : NLL.History) (out : NLL.Reply) : Prop :=
 Calls H proof raw batch (sites roots) NKV_ParentSource.zeroI NKV_ParentSource.zeroV history out
end NLL_Parent
end

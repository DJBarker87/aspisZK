import NLL_ParentInvocation
import NLL_AbortInvocation
set_option autoImplicit false
noncomputable section
namespace NLL_Parent
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Complete parent abort cut chain. A child abort has no returned arrays,
Rust Result or later call. Earlier successful trees thread BOTH arrays. -/
inductive AbortCalls (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize) (batch : Usize) :
 List Call → NLL.Indices → NLL.Values → NLL.History → Pending → Prop where
 | here (root : NLL.Root) (kind : Usize) (rest : List Call) (idx : NLL.Indices) (val : NLL.Values)
   (events : List Event) (pending : Pending)
   (child : AbortInvocation H proof raw root batch kind idx val events pending) :
   AbortCalls H proof raw batch ((root,kind)::rest) idx val (leafHistory kind events) pending
 | next (root : NLL.Root) (kind : Usize) (rest : List Call) (idx nextIdx : NLL.Indices) (val nextVal : NLL.Values)
   (events : List Event) (history : NLL.History) (pending : Pending)
   (child : NLL.Invocation H proof raw root batch kind idx val events (.Ok (),nextIdx,nextVal))
   (tail : AbortCalls H proof raw batch rest nextIdx nextVal history pending) :
   AbortCalls H proof raw batch ((root,kind)::rest) idx val (leafHistory kind events++history) pending

def AbortValues (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (roots : Roots) (batch : Usize) (history : NLL.History) (pending : Pending) : Prop :=
 AbortCalls H proof raw batch (sites roots) NKV_ParentSource.zeroI NKV_ParentSource.zeroV history pending
end NLL_Parent
end

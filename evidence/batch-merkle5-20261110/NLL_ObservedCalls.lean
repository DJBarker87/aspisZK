import NLL_TreeAdopted
import NLL_ParentInvocation
import NKV_ParentTrace
set_option autoImplicit false
noncomputable section
namespace NLL_ObservedCalls
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def tree (H : Bytes → State) (proof : Slice U8) (p : OraclePortCompactDraft.Parsed)
 (raw : Array U32 22#usize) (batch kind : Usize) (idx : NLL.Indices) (val : NLL.Values) :
 NLL.History × Result (Unit × NLL.Indices × NLL.Values) :=
 let model:=eval H (MultiproofConeSlotState.slotState p (Port4B_KeyInstall.queries raw) batch.val kind.val
   (nodeView H proof (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind))
   (NJV_EntryABI.initial idx val 0#usize))
 (model.1,NKV_TailModel.model model.2)

def calls (H : Bytes → State) (proof : Slice U8) (p : OraclePortCompactDraft.Parsed)
 (raw : Array U32 22#usize) (batch : Usize) : List Call → NLL.Indices → NLL.Values → NLL.History × Result Unit
 | [],_,_ => ([],ok ())
 | (_,kind)::rest,idx,val => NKV_ParentTrace.bindRejected (tree H proof p raw batch kind idx val)
     (fun i v => calls H proof p raw batch rest i v)
end NLL_ObservedCalls
end

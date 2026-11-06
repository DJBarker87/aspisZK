import NLL_ParentAbortInvocation
import NLL_TreeAbort
import NLL_AppendPrefix
set_option autoImplicit false
noncomputable section
namespace NLL_ParentAbort
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem calls (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (batch : Usize) (hb : batch.val<2)
 (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (sites : List Call) (kinds : ∀ c∈sites,c.2.val<3)
 (idx : NLL.Indices) (val : NLL.Values) (history : NLL.History) (pending : Pending)
 (native : AbortCalls H proof raw batch sites idx val history pending) :
 NLL_Prefix.At (plan H proof p raw batch sites idx val) (history++pending.answered) pending.parts := by
 induction native with
 | here root kind rest idx val events pending child =>
   have prefixAt:=NLL_TreeAbort.source H proof len p wire raw root batch kind hb
     (kinds (root,kind) (by simp)) canonical idx val events pending child
   exact NLL_AppendPrefix.suffix _ _ _ _ prefixAt
 | next root kind rest idx nextIdx val nextVal events history pending child tail ih =>
   have packet:=NLL_TreeReturning.source H proof len p wire raw root batch kind hb
     (kinds (root,kind) (by simp)) canonical idx val events (.Ok (),nextIdx,nextVal) child
   have next:=ih (fun c mem=>kinds c (List.mem_cons_of_mem _ mem))
   simp only [plan,packet.1,←packet.2,List.append_assoc]
   exact NLL_AppendPrefix.prior _ _ _ _ next

set_option pp.proofs false
#print calls
#print axioms calls
end NLL_ParentAbort
end

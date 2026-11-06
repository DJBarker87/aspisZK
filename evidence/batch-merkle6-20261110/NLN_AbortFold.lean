import NLN_TreePacket
import NLL_ParentAbortInvocation
import NLL_TreeAbort
import NLL_AppendPrefix
set_option autoImplicit false
noncomputable section
namespace NLN_AbortFold
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem calls (H : Bytes → State) (proof : Slice U8)
 (p : OraclePortCompactDraft.Parsed)
 (raw : Array U32 22#usize) (batch : Usize)
 (sites : List Call)
 (packets : ∀ c∈sites,NLN.TreePacket H proof p raw c.1 batch c.2)
 (idx : NLL.Indices) (val : NLL.Values) (history : NLL.History) (pending : Pending)
 (native : AbortCalls H proof raw batch sites idx val history pending) :
 NLL_Prefix.At (plan H proof p raw batch sites idx val) (history++pending.answered) pending.parts := by
 induction native with
 | here root kind rest idx val events pending child =>
   have prefixAt:=(packets (root,kind) (by simp)).aborting idx val events pending child
   exact NLL_AppendPrefix.suffix _ _ _ _ prefixAt.1
 | next root kind rest idx nextIdx val nextVal events history pending child tail ih =>
   have packet:=(packets (root,kind) (by simp)).returning idx val events (.Ok (),nextIdx,nextVal) child
   have next:=ih (fun c mem=>packets c (List.mem_cons_of_mem _ mem))
   simp only [plan,packet.1,←packet.2.1,List.append_assoc]
   exact NLL_AppendPrefix.prior _ _ _ _ next

set_option pp.proofs false
#print calls
#print axioms calls
end NLN_AbortFold
end

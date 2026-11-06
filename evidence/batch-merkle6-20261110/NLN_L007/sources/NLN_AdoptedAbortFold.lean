import NLN_TreePacket
import NLL_AdoptedAbort
import NLL_ParentAbortInvocation
set_option autoImplicit false
noncomputable section
namespace NLN_AdoptedAbortFold
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem source (H : Bytes → State) (proof : Slice U8)
 (p : OraclePortCompactDraft.Parsed)
 (raw : Array U32 22#usize) (batch : Usize)
 (sites : List Call)
 (packets : ∀ c∈sites,NLN.TreePacket H proof p raw c.1 batch c.2)
 (idx : NLL.Indices) (val : NLL.Values) (history : NLL.History) (pending : Pending)
 (native : AbortCalls H proof raw batch sites idx val history pending) :
 NLL_Prefix.At (NLL_ObservedCalls.calls H proof p raw batch sites idx val).1 (history++pending.answered) pending.parts := by
 induction native with
 | here root kind rest idx val events pending child =>
   have known:=(packets (root,kind) (by simp)).aborting idx val events pending child
   exact NLL_AdoptedAbort.bind _ _ _ _ known.2
 | next root kind rest idx nextIdx val nextVal events history pending child tail ih =>
   have packet:=(packets (root,kind) (by simp)).returning idx val events (.Ok (),nextIdx,nextVal) child
   have packet:=packet.2.2
   change (leafHistory kind events,NKV_ReturnBoundary.reject (ok (.Ok (),nextIdx,nextVal)))=
     NLL_ObservedCalls.tree H proof p raw batch kind idx val at packet
   have next:=ih (fun c mem=>packets c (List.mem_cons_of_mem _ mem))
   rw [NLL_ObservedCalls.calls,←packet]
   simp only [NKV_ReturnBoundary.reject,NKV_ParentTrace.bindRejected,List.append_assoc]
   exact NLL_AppendPrefix.prior _ _ _ _ next

set_option pp.proofs false
#print source
#print axioms source
end NLN_AdoptedAbortFold
end

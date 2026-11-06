import NLN_TreePacket
import NLL_ObservedCalls
set_option autoImplicit false
noncomputable section
namespace NLN_AdoptedFold
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem source (H : Bytes → State) (proof : Slice U8)
 (p : OraclePortCompactDraft.Parsed)
 (raw : Array U32 22#usize) (batch : Usize)
 (sites : List Call)
 (packets : ∀ c∈sites,NLN.TreePacket H proof p raw c.1 batch c.2)
 (idx : NLL.Indices) (val : NLL.Values) (history : NLL.History) (out : NLL.Reply)
 (native : Calls H proof raw batch sites idx val history out) :
 NLL_ObservedCalls.calls H proof p raw batch sites idx val=(history,NKV_ParentSource.observe (ok out)) := by
 induction native with
 | nil idx val => rfl
 | error root kind rest idx nextIdx val nextVal events error child =>
   have packet:=(packets (root,kind) (by simp)).returning idx val events (.Err error,nextIdx,nextVal) child
   have packet:=packet.2.2
   change (leafHistory kind events,NKV_ReturnBoundary.reject (ok (.Err error,nextIdx,nextVal)))=
     NLL_ObservedCalls.tree H proof p raw batch kind idx val at packet
   rw [NLL_ObservedCalls.calls,←packet]
   rfl
 | next root kind rest idx nextIdx val nextVal events tailHistory out child tail ih =>
   have packet:=(packets (root,kind) (by simp)).returning idx val events (.Ok (),nextIdx,nextVal) child
   have packet:=packet.2.2
   change (leafHistory kind events,NKV_ReturnBoundary.reject (ok (.Ok (),nextIdx,nextVal)))=
     NLL_ObservedCalls.tree H proof p raw batch kind idx val at packet
   have next:=ih (fun c mem=>packets c (List.mem_cons_of_mem _ mem))
   rw [NLL_ObservedCalls.calls,←packet]
   simp only [NKV_ReturnBoundary.reject,NKV_ParentTrace.bindRejected]
   rw [next]

set_option pp.proofs false
#print source
#print axioms source
end NLN_AdoptedFold
end

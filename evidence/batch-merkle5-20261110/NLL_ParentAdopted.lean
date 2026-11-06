import NLL_ObservedCalls
set_option autoImplicit false
noncomputable section
namespace NLL_ParentAdopted
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem source (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (batch : Usize) (hb : batch.val<2)
 (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (sites : List Call) (kinds : ∀ c∈sites,c.2.val<3)
 (roots : ∀ c∈sites,c.1=encodeState (OraclePortBatchDraft.committedRoot p c.2.val))
 (idx : NLL.Indices) (val : NLL.Values) (history : NLL.History) (out : NLL.Reply)
 (native : Calls H proof raw batch sites idx val history out) :
 NLL_ObservedCalls.calls H proof p raw batch sites idx val=(history,NKV_ParentSource.observe (ok out)) := by
 induction native with
 | nil idx val => rfl
 | error root kind rest idx nextIdx val nextVal events error child =>
   have packet:=NLL_TreeAdopted.returning H proof len p wire raw root batch kind hb
     (kinds (root,kind) (by simp)) canonical (roots (root,kind) (by simp)) idx val events (.Err error,nextIdx,nextVal) child
   change (leafHistory kind events,NKV_ReturnBoundary.reject (ok (.Err error,nextIdx,nextVal)))=
     NLL_ObservedCalls.tree H proof p raw batch kind idx val at packet
   rw [NLL_ObservedCalls.calls,←packet]
   rfl
 | next root kind rest idx nextIdx val nextVal events tailHistory out child tail ih =>
   have packet:=NLL_TreeAdopted.returning H proof len p wire raw root batch kind hb
     (kinds (root,kind) (by simp)) canonical (roots (root,kind) (by simp)) idx val events (.Ok (),nextIdx,nextVal) child
   change (leafHistory kind events,NKV_ReturnBoundary.reject (ok (.Ok (),nextIdx,nextVal)))=
     NLL_ObservedCalls.tree H proof p raw batch kind idx val at packet
   have next:=ih (fun c mem=>kinds c (List.mem_cons_of_mem _ mem)) (fun c mem=>roots c (List.mem_cons_of_mem _ mem))
   rw [NLL_ObservedCalls.calls,←packet]
   simp only [NKV_ReturnBoundary.reject,NKV_ParentTrace.bindRejected]
   rw [next]

set_option pp.proofs false
#print source
#print axioms source
end NLL_ParentAdopted
end

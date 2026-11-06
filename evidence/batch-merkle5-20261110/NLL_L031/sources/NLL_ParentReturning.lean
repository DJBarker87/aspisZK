import NLL_ParentInvocation
set_option autoImplicit false
noncomputable section
namespace NLL_ParentReturning
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Parent composition at the three literal SAME calls. This intermediate
fold installs the actual tree packet on every entered call, threads BOTH
arrays, and retains the first-error prefix without a later invocation. -/
theorem calls (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (batch : Usize) (hb : batch.val<2)
 (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (sites : List Call) (kinds : ∀ c∈sites,c.2.val<3)
 (idx : NLL.Indices) (val : NLL.Values) (history : NLL.History) (out : NLL.Reply)
 (native : Calls H proof raw batch sites idx val history out) :
 model H proof raw batch sites idx val=ok out ∧ plan H proof p raw batch sites idx val=history := by
 induction native with
 | nil idx val => exact ⟨rfl,rfl⟩
 | error root kind rest idx nextIdx val nextVal events error child =>
   have packet:=NLL_TreeReturning.source H proof len p wire raw root batch kind hb
     (kinds (root,kind) (by simp)) canonical idx val events (.Err error,nextIdx,nextVal) child
   constructor
   · simp only [model,packet.1,NKV_ParentSource.next,bind_tc_ok]
     rfl
   · simp only [plan,packet.1,List.append_nil]
     exact packet.2.symm
 | next root kind rest idx nextIdx val nextVal events tailHistory out child tail ih =>
   have packet:=NLL_TreeReturning.source H proof len p wire raw root batch kind hb
     (kinds (root,kind) (by simp)) canonical idx val events (.Ok (),nextIdx,nextVal) child
   have next:=ih (fun c mem=>kinds c (List.mem_cons_of_mem _ mem))
   constructor
   · simp only [model,packet.1,NKV_ParentSource.next,bind_tc_ok]
     exact next.1
   · simp only [plan,packet.1]
     rw [packet.2,next.2]

set_option pp.proofs false
#print calls
#print axioms calls
end NLL_ParentReturning
end

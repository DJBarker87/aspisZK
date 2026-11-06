import NLN_TreePacket
import NLL_ParentInvocation
set_option autoImplicit false
noncomputable section
namespace NLN_ReturningFold
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Parent composition at the three literal SAME calls. This intermediate
fold installs the actual tree packet on every entered call, threads BOTH
arrays, and retains the first-error prefix without a later invocation. -/
theorem calls (H : Bytes → State) (proof : Slice U8)
 (p : OraclePortCompactDraft.Parsed)
 (raw : Array U32 22#usize) (batch : Usize)
 (sites : List Call)
 (packets : ∀ c∈sites,NLN.TreePacket H proof p raw c.1 batch c.2)
 (idx : NLL.Indices) (val : NLL.Values) (history : NLL.History) (out : NLL.Reply)
 (native : Calls H proof raw batch sites idx val history out) :
 model H proof raw batch sites idx val=ok out ∧ plan H proof p raw batch sites idx val=history := by
 induction native with
 | nil idx val => exact ⟨rfl,rfl⟩
 | error root kind rest idx nextIdx val nextVal events error child =>
   have packet:=(packets (root,kind) (by simp)).returning idx val events (.Err error,nextIdx,nextVal) child
   constructor
   · simp only [model,packet.1,NKV_ParentSource.next,bind_tc_ok]
     rfl
   · simp only [plan,packet.1,List.append_nil]
     exact packet.2.1.symm
 | next root kind rest idx nextIdx val nextVal events tailHistory out child tail ih =>
   have packet:=(packets (root,kind) (by simp)).returning idx val events (.Ok (),nextIdx,nextVal) child
   have next:=ih (fun c mem=>packets c (List.mem_cons_of_mem _ mem))
   constructor
   · simp only [model,packet.1,NKV_ParentSource.next,bind_tc_ok]
     exact next.1
   · simp only [plan,packet.1]
     rw [packet.2.1,next.2]

set_option pp.proofs false
#print calls
#print axioms calls
end NLN_ReturningFold
end

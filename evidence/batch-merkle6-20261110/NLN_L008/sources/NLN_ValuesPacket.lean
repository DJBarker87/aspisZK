import NLN_ReturningFold
import NLN_AdoptedFold
import NLN_AbortFold
import NLN_AdoptedAbortFold
import NLL_ParentSource
import NLL_ValuesReturning
set_option autoImplicit false
noncomputable section
namespace NLN
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

structure ValuesPacket (H : Bytes → State) (proof : Slice U8)
 (p : OraclePortCompactDraft.Parsed) (raw : Array U32 22#usize)
 (roots : Roots) (batch : Usize) : Prop where
 returning : ∀ (history : NLL.History) (out : NLL.Reply),
   NLL_Parent.Invocation H proof raw roots batch history out →
   NKV_FRef.verifier.candidate.batch_merkle_values (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
     proof raw roots batch ()=ok out ∧
   plan H proof p raw batch (sites roots) NKV_ParentSource.zeroI NKV_ParentSource.zeroV=history ∧
   NLL_ObservedCalls.calls H proof p raw batch (sites roots) NKV_ParentSource.zeroI NKV_ParentSource.zeroV=
     (history,NKV_ParentSource.observe (ok out))
 aborting : ∀ (history : NLL.History) (pending : Pending),
   AbortValues H proof raw roots batch history pending →
   NLL_Prefix.At (plan H proof p raw batch (sites roots) NKV_ParentSource.zeroI NKV_ParentSource.zeroV)
     (history++pending.answered) pending.parts ∧
   NLL_Prefix.At (NLL_ObservedCalls.calls H proof p raw batch (sites roots)
     NKV_ParentSource.zeroI NKV_ParentSource.zeroV).1 (history++pending.answered) pending.parts

theorem values (H : Bytes → State) (proof : Slice U8) (p : OraclePortCompactDraft.Parsed)
 (raw : Array U32 22#usize) (roots : Roots) (batch : Usize)
 (trees : ∀ c∈sites roots,TreePacket H proof p raw c.1 batch c.2) :
 ValuesPacket H proof p raw roots batch := by
 constructor
 · intro history out native
   obtain ⟨value,historyLaw⟩:=NLN_ReturningFold.calls H proof p raw batch (sites roots) trees
     NKV_ParentSource.zeroI NKV_ParentSource.zeroV history out native
   refine ⟨(NLL_ParentSource.source H proof raw roots batch).trans value,historyLaw,?_⟩
   exact NLN_AdoptedFold.source H proof p raw batch (sites roots) trees
     NKV_ParentSource.zeroI NKV_ParentSource.zeroV history out native
 · intro history pending native
   exact ⟨NLN_AbortFold.calls H proof p raw batch (sites roots) trees
       NKV_ParentSource.zeroI NKV_ParentSource.zeroV history pending native,
     NLN_AdoptedAbortFold.source H proof p raw batch (sites roots) trees
       NKV_ParentSource.zeroI NKV_ParentSource.zeroV history pending native⟩

/-- All three entered sites use exactly the corresponding parent root input. -/
theorem bindings (p : OraclePortCompactDraft.Parsed) (roots : Roots)
 (rootValues : ∀ k,k<3 → Port3_NativeBatchCalls.rootAt roots k=
   encodeState (OraclePortBatchDraft.committedRoot p k)) :
 ∀ c∈sites roots,c.1=encodeState (OraclePortBatchDraft.committedRoot p c.2.val) := by
 intro c mem
 simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at mem
 rcases mem with rfl|rfl|rfl
 · exact rootValues 0 (by omega)
 · exact rootValues 1 (by omega)
 · exact rootValues 2 (by omega)

set_option pp.proofs false
#print ValuesPacket
#print values
#print axioms values
#print axioms bindings
end NLN
end

import NLN_ValuesPacket
import NLL_BatchSource
import NLL_BatchAbort
set_option autoImplicit false
noncomputable section
namespace NLN
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

structure BatchPacket (H : Bytes → State) (proof : Slice U8)
 (parsed : OraclePortCompactDraft.Parsed) (p : verifier.Prepared)
 (folded : NLL.Root) (batch : Usize) : Prop where
 returning : ∀ (history : NLL.History) (out : NLL.Reply),
   NLL_BatchSource.Invocation H proof p folded batch history out →
   NKV_FRef.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
     proof p folded batch ()=ok out ∧
   plan H proof parsed p.queries batch (sites (NLL_BatchSource.roots p folded))
     NKV_ParentSource.zeroI NKV_ParentSource.zeroV=history ∧
   NLL_ObservedCalls.calls H proof parsed p.queries batch (sites (NLL_BatchSource.roots p folded))
     NKV_ParentSource.zeroI NKV_ParentSource.zeroV=(history,NKV_ParentSource.observe (ok out))
 aborting : ∀ (history : NLL.History) (pending : Pending),
   NLL_BatchAbort.Invocation H proof p folded batch history pending →
   NLL_Prefix.At (plan H proof parsed p.queries batch (sites (NLL_BatchSource.roots p folded))
     NKV_ParentSource.zeroI NKV_ParentSource.zeroV) (history++pending.answered) pending.parts ∧
   NLL_Prefix.At (NLL_ObservedCalls.calls H proof parsed p.queries batch (sites (NLL_BatchSource.roots p folded))
     NKV_ParentSource.zeroI NKV_ParentSource.zeroV).1 (history++pending.answered) pending.parts

theorem batch (H : Bytes → State) (proof : Slice U8) (parsed : OraclePortCompactDraft.Parsed)
 (p : verifier.Prepared) (folded : NLL.Root) (batch : Usize)
 (child : ValuesPacket H proof parsed p.queries (NLL_BatchSource.roots p folded) batch) :
 BatchPacket H proof parsed p folded batch := by
 constructor
 · intro history out native
   obtain ⟨value,historyLaw,observed⟩:=child.returning history out native
   exact ⟨(NLL_BatchSource.source H proof p folded batch).trans value,historyLaw,observed⟩
 · exact child.aborting

set_option pp.proofs false
#print BatchPacket
#print batch
#print axioms batch
end NLN
end

import NLL_BatchReturning
import NLL_BatchAbort
set_option autoImplicit false
noncomputable section
namespace NLL_PhysicalPlan
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Merkle processing uses Parsed.wire only. This local plan chooses its wire
from the physical proof itself; no parser success or selected leaf payload is
assumed. It is not substituted for the headline Parsed semantic provenance. -/
def physical (proof : Slice U8) : OraclePortCompactDraft.Parsed :=
 ⟨MultiproofConeCanonical.bytesOf proof.val,[]⟩

theorem returning (H : Bytes → State) (proof : Array U8 57607#usize)
 (p : verifier.Prepared) (folded : NLL.Root) (batch : Usize) (hb : batch.val<2)
 (canonical : ∀ j,j<22 → p.queries.val[j]!.val<262144)
 (history : NLL.History) (out : NLL.Reply)
 (native : NLL_BatchSource.Invocation H proof.to_slice p folded batch history out) :
 NKV_FRef.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
   proof.to_slice p folded batch ()=ok out ∧
 plan H proof.to_slice (physical proof.to_slice) p.queries batch (sites (NLL_BatchSource.roots p folded))
   NKV_ParentSource.zeroI NKV_ParentSource.zeroV=history :=
 NLL_BatchReturning.source H proof.to_slice proof.property (physical proof.to_slice) rfl p folded batch hb canonical history out native

theorem abort (H : Bytes → State) (proof : Array U8 57607#usize)
 (p : verifier.Prepared) (folded : NLL.Root) (batch : Usize) (hb : batch.val<2)
 (canonical : ∀ j,j<22 → p.queries.val[j]!.val<262144)
 (history : NLL.History) (pending : Pending)
 (native : NLL_BatchAbort.Invocation H proof.to_slice p folded batch history pending) :
 NLL_Prefix.At (plan H proof.to_slice (physical proof.to_slice) p.queries batch (sites (NLL_BatchSource.roots p folded))
   NKV_ParentSource.zeroI NKV_ParentSource.zeroV) (history++pending.answered) pending.parts :=
 NLL_BatchAbort.source H proof.to_slice proof.property (physical proof.to_slice) rfl p folded batch hb canonical history pending native

set_option pp.proofs false
#print returning
#print abort
#print axioms returning
#print axioms abort
end NLL_PhysicalPlan
end

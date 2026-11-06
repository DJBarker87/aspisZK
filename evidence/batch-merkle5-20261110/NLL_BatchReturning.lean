import NLL_BatchSource
set_option autoImplicit false
noncomputable section
namespace NLL_BatchReturning
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem source (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val)
 (p : verifier.Prepared) (folded : NLL.Root) (batch : Usize) (hb : batch.val<2)
 (canonical : ∀ j,j<22 → p.queries.val[j]!.val<262144)
 (history : NLL.History) (out : NLL.Reply)
 (native : NLL_BatchSource.Invocation H proof p folded batch history out) :
 NKV_FRef.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
   proof p folded batch ()=ok out ∧
 plan H proof parsed p.queries batch (sites (NLL_BatchSource.roots p folded))
   NKV_ParentSource.zeroI NKV_ParentSource.zeroV=history := by
 rw [NLL_BatchSource.source]
 exact NLL_ValuesReturning.source H proof len parsed wire p.queries _ batch hb canonical history out native

set_option pp.proofs false
#print source
#print axioms source
end NLL_BatchReturning
end

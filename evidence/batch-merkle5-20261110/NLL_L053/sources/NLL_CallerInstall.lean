import NLL_PhysicalPlan
import NLL_CallerCarrier
set_option autoImplicit false
noncomputable section
namespace NLL_CallerInstall
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- An intermediate SAME Prepared installation, not a positive row root.
BodyMatches must itself be produced by the actual caller; packaging it as a
premise does not discharge that source/runtime provenance obligation. -/
theorem returning (H : Bytes → State) (proof : Array U8 57607#usize)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (pm : OraclePortCheckpointAbiC5.Prepared)
 (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
 (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am)
 (folded : NLL.Root) (batch : Usize) (hb : batch.val<2)
 (history : NLL.History) (out : NLL.Reply)
 (native : NLL_BatchSource.Invocation H proof.to_slice p folded batch history out) :
 NKV_FRef.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
   proof.to_slice p folded batch ()=ok out ∧
 plan H proof.to_slice (NLL_PhysicalPlan.physical proof.to_slice) p.queries batch (sites (NLL_BatchSource.roots p folded))
   NKV_ParentSource.zeroI NKV_ParentSource.zeroV=history :=
 NLL_PhysicalPlan.returning H proof p folded batch hb (NLL_CallerCarrier.canonical p a pm am fields) history out native

set_option pp.proofs false
#print returning
#print axioms returning
end NLL_CallerInstall
end

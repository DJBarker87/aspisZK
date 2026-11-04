import NGC_InitialInvariant
import NGC_WriterDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_PrestateBridge
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes3Namespaces
/-- Initializer observations, then the SAME successful query loop, then the
SAME pending finish. Preparation Fields and native pending installation are
named upstream boundaries; no independent initial/post invariant is assumed. -/
theorem from_initializers (constructors : VTop_Stages.Ops) (reserveA reserveB : Bool)
 (base : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geometry : verifier.QueryGeometry)
 (b pending : verifier.BatchedWeights) (prepared : NGC_PreparationBoundary.Fields p)
 (newA : (Port3_Constructor.installed constructors reserveA).op12 .S2=ok (.Ok a))
 (newB : Port3_NativePendingInstall.source reserveB a.weights.deref=ok (.Ok b))
 (accepted : Port3_NativeQueryBody.verifier.candidate.query_loop (NFS_QueryOps.installed base)
  proof p a g none geometry b 10#usize=ok (.Ok (after,pending))) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 let written : verifier.Accumulator := {after with weights:=⟨out.val,out.property⟩}
 NGC_KNE_Caller.WriterDomain (toPrepared p) (toAccumulator written) ∧
 written.rhs=after.rhs ∧ written.power=after.power ∧ written.next=after.next := by
 have initial := NGC_InitialInvariant.initial constructors reserveA reserveB p a b prepared newA newB
 exact NGC_WriterDomain.from_query_loop base proof p a after g geometry b pending
  initial.1 initial.2 prepared accepted
#print axioms from_initializers
end AspisR1.NGC_PrestateBridge
end

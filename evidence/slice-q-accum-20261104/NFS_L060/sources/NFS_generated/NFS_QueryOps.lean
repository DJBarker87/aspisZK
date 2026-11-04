import NFS_AccumInstall
import NFP_DotCaller
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_QueryOps
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
/-- Install exactly the closed accumulation dictionary and the line child.
Other root-owned operations (opening, decoding, circle and trace) are kept. -/
def base (ops : Ops) : Ops := {ops with op16 := SAQ_LineQuery.line}
def installed (ops : Ops) : Ops :=
 NFP_ObserverErasure.erase
  (NFP_DotInstall.cohort (NBO_AccumulateAssociation.sourceOps (NFS_NEV_TailModel.fields (base ops))))

theorem line (ops : Ops) : (installed ops).op16=SAQ_LineQuery.line := rfl
/-- Phase erasure does not change any accumulation instruction: its sole
trace callback is already the exact unit-valued trace model. -/
theorem accumulation (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (node : U32) (value : NFP_QueryCuts.E) (b : verifier.BatchedWeights) :
 verifier.accumulate_batched_with_node (installed ops) p a node value b =
 verifier.accumulate_batched_with_node
  (NBO_AccumulateAssociation.sourceOps (NFS_NEV_TailModel.fields (base ops))) p a node value b := rfl
#print axioms line
#print axioms accumulation
end AspisR1.NFS_QueryOps
end

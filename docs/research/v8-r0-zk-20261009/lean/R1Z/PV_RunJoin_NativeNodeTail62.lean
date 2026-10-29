import R1Z.PV_RunJoin_NativeActual62
import R1Z.PV_RunJoin_NodeActualSlots60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeNodeTail62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual62
open PV_RunJoin_PublishSkeleton54

/-- The complete six-slot append equation at the unchanged ActualRun plans.
The independent sorted/deduplicated publication-indices conjunct remains. -/
theorem append (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops
    ∀ (phase : PV_RunJoin_NativeActual62.P base heap box ops) (p : prover.Publication)
      (out : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment),
      PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_NativeActual62.runs base heap box ops phase) p →
      p.backend.c1=some cc1 → p.backend.c2=some cc2 →
      out.length=(PV_RunJoin_NativeActual62.runs base heap box ops phase).plan.offNodes →
      resultBytes (prover.append_node_slots out cc1 cc2 p.tree p.queries)=
        exceptBytes (ProverCommitPublish43.slots
          (PV_RunJoin_NativeActual62.runs base heap box ops phase).plan.slots (bytes out.val)) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  intro phase p out cc1 cc2 context hc1 hc2 hlen
  change resultBytes (prover.append_node_slots out cc1 cc2 p.tree p.queries)=
    exceptBytes (ProverCommitPublish43.slots (PV_RunJoin_ActualRun.plans phase.val).slots (bytes out.val))
  rw [PV_RunJoin_NodeActualSlots60.actual phase.val p cc1 cc2 context hc1 hc2]
  erw [PV_RunJoin_NodeSixSequence60.source (baseTypes base) heap box (residual base ops)]
  apply PV_RunJoin_NodeSequence60.complete
  change out.length=28359 at hlen
  change out.length+2*(4672+4672+4096+5504+5504+4800)≤Usize.max
  rw [hlen]
  scalar_tac

#print axioms append
end R1Z.PV_RunJoin_NativeNodeTail62

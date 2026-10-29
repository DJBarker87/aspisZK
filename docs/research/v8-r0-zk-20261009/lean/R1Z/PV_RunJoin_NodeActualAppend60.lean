import R1Z.PV_RunJoin_NodeActualSlots60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeActualAppend60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46 PV_RunJoin_PublishSkeleton54
open PV_RunJoin_NativeControl55 (Phase)

theorem actual (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∀ (phase : Phase) (p : prover.Publication) (out : alloc.vec.Vec U8)
      (cc1 cc2 : host_commitment.Commitment),
      PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p →
      p.backend.c1=some cc1 → p.backend.c2=some cc2 → out.length=28359 →
      resultBytes (prover.append_node_slots out cc1 cc2 p.tree p.queries)=
        exceptBytes (ProverCommitPublish43.slots (PV_RunJoin_ActualRun.plans phase).slots (bytes out.val)) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  intro phase p out cc1 cc2 context hc1 hc2 offset
  rw [PV_RunJoin_NodeSixSequence60.source base heap box ops]
  rw [PV_RunJoin_NodeActualSlots60.actual phase p cc1 cc2 context hc1 hc2]
  apply PV_RunJoin_NodeSequence60.complete
  have hs := ProverCommitPairCounter47.usize_large
  rw [UScalar.size_def] at hs
  rw [offset]
  change 28359+2*29248≤Usize.max
  omega

#print axioms actual
end R1Z.PV_RunJoin_NodeActualAppend60

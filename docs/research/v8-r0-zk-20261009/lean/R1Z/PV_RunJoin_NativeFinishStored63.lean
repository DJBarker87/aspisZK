import R1Z.PV_RunJoin_FinishStored63
import R1Z.PV_RunJoin_NativeActual63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeFinishStored63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_PublishSkeleton54

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : @PV_RunJoin_NativeControl55.Phase (types base)) (p : prover.Publication)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base) (opsNative base heap box ops runtime world)
      (@PV_RunJoin_ActualRun.runs (types base) (opsNative base heap box ops runtime world) phase) p) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    bytes p.root.val=(PV_RunJoin_ActualRun.plans phase).root ∧
      (∃ ib, aspis_core.field.wide_exact.WideExact.to_le_bytes p.inactive=ok ib ∧
        bytes ib.val=(PV_RunJoin_ActualRun.plans phase).inactive) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  refine ⟨(PV_RunJoin_ActualPlanProjection60.root phase p context).symm,?_⟩
  exact PV_RunJoin_FinishStored63.inactive (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) phase p context

#print axioms complete
end R1Z.PV_RunJoin_NativeFinishStored63

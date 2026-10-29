import R1Z.PV_RunJoin_NativeActual63
import R1Z.PV_RunJoin_ActualPreparedCanonical60
import R1Z.PV_RunJoin_ActualAlpha1Canonical60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeFinishCanonical63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open ProverCommitWideOps48

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : @PV_RunJoin_NativeControl55.Phase (types base)) (prepared : prover.PreparedOpening)
    (success : @prover.prepare_opening (types base) (opsNative base heap box ops runtime world)
      .S2 phase.hash phase.backend phase.sem=ok (.Ok prepared)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    canonical (PV_RunJoin_ActualRun.data phase).g ∧ canonical (PV_RunJoin_ActualRun.data phase).k ∧
      canonical (PV_RunJoin_ActualRun.data phase).a ∧ canonical (PV_RunJoin_ActualRun.data phase).b := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨hg,hk,ha⟩ := PV_RunJoin_ActualPreparedCanonical60.complete
    (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world) phase prepared success
  exact ⟨hg,hk,ha,PV_RunJoin_ActualAlpha1Canonical60.complete
    (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world) phase⟩

#print axioms complete
end R1Z.PV_RunJoin_NativeFinishCanonical63

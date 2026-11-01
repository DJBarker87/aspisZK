import R1Z.PV_RunJoin_NativeBackendMatrix66
import R1Z.PV_RunJoin_NativeEncoderBinding66
import R1Z.PV_RunJoin_ClaimDomain66
import R1Z.PV_RunJoin_PrepareClaimInputs51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeClaimDomain66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (prepared : @prover.PreparedOpening (types base))
    (hp : letI : ExternalTypes := types base
      @prover.prepare_opening (types base) (opsNative base heap box ops runtime world)
        .S2 phase.val.hash phase.val.backend phase.val.sem=ok (.Ok prepared)) :
    prepared.y1.length=32*29 ∧ PV_RunJoin_HighDomain40.HighZero prepared.y1.val := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have matrix := PV_RunJoin_NativeBackendMatrix66.complete base heap box ops runtime world phase
  have input : alloc.vec.Vec.deref phase.val.backend.messages=
      PV_RunJoin_CoefficientsWeight46.messages (fun l j => ProverRwDictionaryTower.fromW
        (ProverCommitNativeOps47.embedded ((PV_RunJoin_ActualRun.data phase.val).c l j))) := by
    rw [matrix]
    rfl
  obtain ⟨hx,hy⟩ := PV_RunJoin_SemanticClaimPoint50.canonical phase.val.sem.z
  have domain := PV_RunJoin_ClaimDomain66.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) (PV_RunJoin_ActualRun.data phase.val).c
    (PV_RunJoin_ActualData59.canonical_coefficients phase.val)
    (PV_RunJoin_SemanticClaimPoint50.x phase.val.sem.z)
    (PV_RunJoin_SemanticClaimPoint50.y phase.val.sem.z) hx hy
  dsimp only at domain
  rw [PV_RunJoin_NativeEncoderBinding66.residual base ops runtime world] at domain
  obtain ⟨known,claim,hknown,hclaim,length,high⟩ := domain
  obtain ⟨_,actual,ha,hactual⟩ := PV_RunJoin_PrepareClaimInputs51.complete
    (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world)
    .S2 phase.val.hash phase.val.backend phase.val.sem prepared hp
  rw [input] at ha
  have coeffEq : actual=known := Result.ok.inj (ha.symm.trans hknown)
  rw [coeffEq] at hactual
  have claimEq : prepared.y1=claim := Result.ok.inj (hactual.symm.trans hclaim)
  rw [claimEq]
  exact ⟨length,high⟩

#print axioms complete
end R1Z.PV_RunJoin_NativeClaimDomain66

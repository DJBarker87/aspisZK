import R1Z.PV_RunJoin_NativeActual63
import R1Z.PV_RunJoin_ProducedOrigin61
import R1Z.PV_RunJoin_BuildMaterialBackendLength58
import R1Z.PV_RunJoin_PrepareClaimInputs51
import R1Z.PV_RunJoin_ClaimLength48
import R1Z.PV_RunJoin_CoefficientsActual50
import R1Z.PV_RunJoin_FinishFrame63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeClaimLength66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem backend {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world) :
    phase.val.backend.messages.length=29 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨_,compiled,noised,maskOnly,d,g,padding,initial,hlen,built⟩ :=
    PV_RunJoin_ProducedOrigin61.origin (PV_RunJoin_NativeResidual62.baseTypes base)
      heap box (residual base ops runtime world) phase.val phase.property
  have h := PV_RunJoin_BuildMaterialBackendLength58.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
    phase.val.public1 compiled noised maskOnly d g padding initial phase.val.hash .S2 hlen
  erw [built] at h
  exact h

theorem prepared {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (p : prover.PreparedOpening)
    (success : @prover.prepare_opening (types base) (opsNative base heap box ops runtime world)
      .S2 phase.val.hash phase.val.backend phase.val.sem=ok (.Ok p)) :
    p.y1.length=32*29 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have length := backend base heap box ops runtime world phase
  obtain ⟨_,coeff,hcoeff,hclaim⟩ := PV_RunJoin_PrepareClaimInputs51.complete
    (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world)
    .S2 phase.val.hash phase.val.backend phase.val.sem p success
  obtain ⟨known,hknown,hval,hlen⟩ := PV_RunJoin_CoefficientsActual50.complete
    (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world)
    (alloc.vec.Vec.deref phase.val.backend.messages) (by change phase.val.backend.messages.length≤14336;omega)
  have eq : coeff=known := Result.ok.inj (hcoeff.symm.trans hknown)
  have lc : coeff.length=29 := by rw [eq,hlen];exact length
  have result := PV_RunJoin_ClaimLength48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) (alloc.vec.Vec.deref coeff)
    (PV_RunJoin_SemanticClaimPoint50.point phase.val.sem.z)
    (by change coeff.length≤14336;omega) p.y1 hclaim
  change p.y1.length=32*coeff.length at result
  rw [lc] at result
  exact result

theorem publication {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (p : prover.Publication)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base) (opsNative base heap box ops runtime world)
      (@PV_RunJoin_ActualRun.runs (types base) (opsNative base heap box ops runtime world) phase.val) p) :
    p.y1.length=32*29 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨prep,salts,hp,hs,hf⟩ := context
  rw [(PV_RunJoin_FinishFrame63.complete .S2 phase.val.hash prep salts p hf).2.2.1]
  exact prepared base heap box ops runtime world phase prep hp

#print axioms backend
#print axioms prepared
#print axioms publication
end R1Z.PV_RunJoin_NativeClaimLength66

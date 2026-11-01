import R1Z.PV_RunJoin_PrepareProducedArraysNative66
import R1Z.PV_RunJoin_NativeClaimLength66
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativePreparedArrays66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_B2_F_ConstructorCarrier (Weight toWeight amap)
open PV_RunJoin_SemanticMaterialInputs50
open ProverRwDictionaryTower (fromW toW)
open PV_RunJoin_CoefficientActualCell50 (Column permuted)
abbrev S := ProverCommitWideOps48.Source
abbrev W := aspis_core.field.wide_exact.WideExact

theorem complete {State Fail : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) State Fail)
    (world : PV_FXM_ReserveWorld.World State Fail)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (prepared : prover.PreparedOpening)
    (hp : letI : ExternalTypes := types base
      @prover.prepare_opening (types base) (opsNative base heap box ops runtime world)
        .S2 phase.val.hash phase.val.backend phase.val.sem=ok (.Ok prepared)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ (coeff : alloc.vec.Vec Column) (kw : Weight) (qSource wSource : Array S 1024#usize)
      (tr : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
      (claim : alloc.vec.Vec U8) (gamma inactive kappa : W) (hlen : coeff.length=29),
      coeff.val=phase.val.backend.messages.val.map permuted ∧
      ProverCommitGammaOutput53.run (PV_RunJoin_GammaActualInputs50.table (alloc.vec.Vec.deref coeff) hlen) (toW gamma)=ok qSource ∧
      ProverCommitWeightsMaterial53.run (ProverCommitQArray48.array 10#usize (alpha phase.val.sem))
        (ProverCommitNativeQ48.source (x0 phase.val.sem)) (ProverCommitNativeQ48.source (y0 phase.val.sem))
        (ProverCommitNativeQ48.source (x1 phase.val.sem)) (ProverCommitNativeQ48.source (y1 phase.val.sem)) (toW kappa)=ok wSource ∧
      box .S2 phase.val.sem.alpha phase.val.phase.val.sem.z=ok () ∧ heap (toWeight kw) kappa=ok .supplied ∧
      @PV_RunJoin_PrepareTail48.run (types base) (opsNative base heap box ops runtime world) .S2 phase.val.hash phase.val.backend phase.val.sem
        tr claim gamma inactive kappa (Array.to_slice (amap fromW qSource))
          (Array.to_slice (amap fromW wSource))=ok (.Ok prepared) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  exact PV_RunJoin_PrepareProducedArraysNative66.complete
    (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world)
    (PV_RunJoin_GammaArrayNative66.residual base ops runtime world)
    phase.val.hash phase.val.backend phase.val.sem
    (PV_RunJoin_NativeClaimLength66.backend base heap box ops runtime world phase) prepared hp
#print axioms complete
end R1Z.PV_RunJoin_NativePreparedArrays66

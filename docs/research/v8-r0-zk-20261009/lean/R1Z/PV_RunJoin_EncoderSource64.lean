import R1Z.PV_RunJoin_NativeFrames63
import R1Z.PV_RDCD4_V201
/-! op79 consumes the RDCD4 complete source/Result packet at WideExact.
The source association is own-1 structural, not an extraction-identity or
machine-code theorem. V370 and D381/D386 remain. No formatting semantics occur
in the encoder packet. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncoderSource64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected

abbrev W := aspis_core.field.wide_exact.WideExact

theorem callback {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    @ExternalFuns.op79 (types base) (opsNative base heap box ops runtime world)=
      fun {E} inst q p => @PV_DL_EncoderControl.value E inst q p := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_79]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem source {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (q : Array W 1024#usize) (p : aspis_core.r0.domain.Point W) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    aspis_core.r0.encoder.eval_message
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField q p=
    PV_RDCD4_V201.value
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField q p := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  change (opsNative base heap box ops runtime world).op79 _ q p=_
  rw [callback]
  exact (PV_DL_EncoderControl.source_reference _ q p).symm.trans
    (PV_RDCD4_V201.source_reference _ q p).symm

#print axioms callback
#print axioms source
end R1Z.PV_RunJoin_EncoderSource64

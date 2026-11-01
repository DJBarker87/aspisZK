import R1Z.PV_RunJoin_NativeBinding63
import R1Z.PV_RunJoin_NativeSample62
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSampleSource66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

/-- Transport the existing complete source facts through the checked native
dictionary identity, retaining the allocator runtime and its world. -/
theorem facts {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (prepared : prover.PreparedOpening)
    (hp : letI : ExternalTypes := types base
      @prover.prepare_opening (types base) (opsNative base heap box ops runtime world)
        .S2 phase.val.hash phase.val.backend phase.val.sem=ok (.Ok prepared)) :
    @PV_RunJoin_ActualSample60.SourceFacts (types base) (opsNative base heap box ops runtime world) phase.val := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have native := PV_RunJoin_NativeBinding63.native base heap box ops runtime world
  let p : PV_RunJoin_NativeActual62.P base heap box (PV_RunJoin_NativeBinding63.remaining base ops runtime world) :=
    ⟨phase.val,by simpa only [←native] using phase.property⟩
  have hp' : @prover.prepare_opening (types base)
      (PV_RunJoin_NativeResidual62.opsNative base heap box (PV_RunJoin_NativeBinding63.remaining base ops runtime world))
      .S2 p.val.hash p.val.backend p.val.sem=ok (.Ok prepared) := by
    simpa only [←native] using hp
  have source := PV_RunJoin_NativeSample62.sourceFacts base heap box
    (PV_RunJoin_NativeBinding63.remaining base ops runtime world) p prepared hp'
  simpa only [←native] using source

theorem sample {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (prepared : prover.PreparedOpening)
    (hp : letI : ExternalTypes := types base
      @prover.prepare_opening (types base) (opsNative base heap box ops runtime world)
        .S2 phase.val.hash phase.val.backend phase.val.sem=ok (.Ok prepared)) :
    PV_RunJoin_OpeningImages54.Sample
      (@PV_RunJoin_ActualRun.data (types base) (opsNative base heap box ops runtime world) phase.val) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  exact PV_RunJoin_ActualSample60.association phase.val (facts base heap box ops runtime world phase prepared hp)

#print axioms facts
#print axioms sample
end R1Z.PV_RunJoin_NativeSampleSource66

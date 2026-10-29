import R1Z.PV_RunJoin_NativeFrames63
import R1Z.PV_RunJoin_ProducedLinks60
/-! Same Produced and nine Links, with the confirmed dictionary packets and
an explicit allocator world. No successful-capture theorem is assumed. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeActual63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

abbrev P {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :=
  @PV_RunJoin_ActualProvenance60.ActualPhase (types base) (opsNative base heap box ops runtime world)

def runs {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    P base heap box ops runtime world → @PV_RunJoin_PublishSkeleton54.Run (types base) :=
  @PV_RunJoin_ActualProvenance60.runs (types base) (opsNative base heap box ops runtime world)

abbrev Links {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :=
  @PV_RunJoin_PublishProduced60.Links (types base) (opsNative base heap box ops runtime world)

#print axioms P
#print axioms runs
#print axioms Links
end R1Z.PV_RunJoin_NativeActual63

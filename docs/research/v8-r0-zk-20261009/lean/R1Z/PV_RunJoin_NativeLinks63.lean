import R1Z.PV_RunJoin_NativeBinding63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeLinks63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem queryContext : @PV_RunJoin_PublishProduced60.PV_RunJoin_Link_QueryContext
    (types base) (opsNative base heap box ops runtime world) :=
  @PV_RunJoin_ProducedLinks60.queryContext (types base) (opsNative base heap box ops runtime world)

theorem queryRange : @PV_RunJoin_PublishProduced60.PV_RunJoin_Link_QueryRange
    (types base) (opsNative base heap box ops runtime world) :=
  @PV_RunJoin_ProducedLinks60.queryRange (types base) (opsNative base heap box ops runtime world)

theorem frontRoom : @PV_RunJoin_ActualFrontRoom61.FrontRoom
    (types base) (opsNative base heap box ops runtime world) := by
  rw [PV_RunJoin_NativeBinding63.native]
  exact PV_RunJoin_NativeFrontRoom62.complete base heap box
    (PV_RunJoin_NativeBinding63.remaining base ops runtime world)

theorem publishOrder : @PV_RunJoin_PublishProduced60.PV_RunJoin_Link_PublishOrder
    (types base) (opsNative base heap box ops runtime world) := by
  rw [PV_RunJoin_NativeBinding63.native]
  exact PV_RunJoin_NativeFrontRoom62.publishOrder base heap box
    (PV_RunJoin_NativeBinding63.remaining base ops runtime world)

#print axioms queryContext
#print axioms queryRange
#print axioms frontRoom
#print axioms publishOrder
end R1Z.PV_RunJoin_NativeLinks63

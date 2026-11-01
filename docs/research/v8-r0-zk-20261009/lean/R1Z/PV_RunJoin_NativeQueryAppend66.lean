import R1Z.PV_RunJoin_NativeQueryDomain66
import R1Z.PV_RunJoin_NativeQueryPrimitive64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeQueryAppend66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    @PV_RunJoin_PublishProduced60.PV_RunJoin_Link_QueryAppend (types base)
      (opsNative base heap box ops runtime world) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  intro phase p fields range context
  refine ⟨(PV_RunJoin_ActualProvenance60.layout phase).1,?_⟩
  intro out cc1 cc2 hc1 hc2 offset
  have domain := PV_RunJoin_NativeQueryDomain66.complete base heap box ops runtime world phase p cc1 cc2 hc1 hc2 context
  exact PV_RunJoin_NativeQueryPrimitive64.complete base heap box ops runtime world phase p cc1 cc2 hc1 hc2
    context domain out offset

#print axioms complete
end R1Z.PV_RunJoin_NativeQueryAppend66

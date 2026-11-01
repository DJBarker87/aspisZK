import R1Z.PV_RunJoin_NativeFinishContext69
import R1Z.PV_RunJoin_NativeFinishDischarge69
import R1Z.PV_RunJoin_NativeOriginalPublication60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeFinishDischarge69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_PublishProduced60

/-- Original links with QueryAppend and FinishContext discharged from source.
The other seven links and actual-domain non-emptiness remain. -/
def Remaining [ExternalTypes] [ExternalFuns] : Prop :=
  PV_RunJoin_Link_R24Sampler ∧ PV_RunJoin_Link_CommonSample ∧
  PV_RunJoin_Link_BackendInput ∧
  PV_RunJoin_Link_QueryContext ∧ PV_RunJoin_Link_QueryRange ∧
  PV_RunJoin_Link_NodeAppend ∧ PV_RunJoin_Link_PublishOrder

theorem links {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (remaining : @Remaining (types base) (opsNative base heap box ops runtime world)) :
    @Links (types base) (opsNative base heap box ops runtime world) := by
  obtain ⟨r24,common,backend,context,range,node,ordering⟩ := remaining
  exact ⟨r24,common,backend,
    PV_RunJoin_NativeFinishContext69.complete base heap box ops runtime world,context,range,
    PV_RunJoin_NativeQueryAppend66.complete base heap box ops runtime world,node,ordering⟩

/-- Original native publication conclusion with the same remaining seven links. -/
theorem publication {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (remaining : @Remaining (types base) (opsNative base heap box ops runtime world))
    {T : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T) :
    PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
      (@PV_RunJoin_NativePublication55.actual (types base) (opsNative base heap box ops runtime world) T store)
      (@PV_RunJoin_NativePublication55.published (types base) (opsNative base heap box ops runtime world) T
        (@PV_RunJoin_ActualRun.data (types base) (opsNative base heap box ops runtime world))
        (@PV_RunJoin_ActualRun.plans (types base) (opsNative base heap box ops runtime world)) store) :=
  PV_RunJoin_NativeOriginalPublication60.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) (links base heap box ops runtime world remaining) store

#print axioms Remaining
#print axioms links
#print axioms publication
end R1Z.PV_RunJoin_NativeFinishDischarge69

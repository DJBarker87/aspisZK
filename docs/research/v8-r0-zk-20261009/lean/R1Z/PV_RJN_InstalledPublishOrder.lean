import R1Z.PV_RJN_LayoutInstalled
import R1Z.PV_RJN_NativePublishOrder
import R1Z.PV_RJN_ContextPublishOrder
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJN_InstalledPublishOrder
open ProverRwFull PV_RunJoin_PublishSkeleton54 PV_RunJoin_WeightInstalled46
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_NativeCallback55 (runOf)
open PV_RJN_LayoutInstalled

theorem actual (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (data : @Phase (types base) → PV_RunJoin_OpeningImages54.Data)
    (plans : @Phase (types base) → Plan)
    (producer_layout : @PV_RJN_Producer_PlanLayout _ (types base) (@runOf (types base) data plans))
    (producer_lengths : @PV_RJN_Producer_FrontLengths _ (types base) (@runOf (types base) data plans)) :
    @PV_RunJoin_PublishContext57.PV_RunJoin_Link_PublishOrder (types base)
      (selected base heap box ops) _ (@runOf (types base) data plans) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  exact PV_RJN_NativePublishOrder.actual data plans
    (PV_RJN_LayoutInstalled.actual base heap box ops _ producer_layout)
    (front_room _ producer_lengths)

/-- The same local source-order proof works with the explicit node correction.
This does not assert that the corrected node link holds or has a witness. -/
theorem contextual (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (data : @Phase (types base) → PV_RunJoin_OpeningImages54.Data)
    (plans : @Phase (types base) → Plan)
    (producer_layout : @PV_RJN_Producer_PlanLayout _ (types base) (@runOf (types base) data plans))
    (producer_lengths : @PV_RJN_Producer_FrontLengths _ (types base) (@runOf (types base) data plans)) :
    @PV_RJN_NodeContext.PV_RJN_Link_PublishOrder (types base)
      (selected base heap box ops) _ (@runOf (types base) data plans) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  exact PV_RJN_ContextPublishOrder.native data plans
    (PV_RJN_LayoutInstalled.actual base heap box ops _ producer_layout)
    (front_room _ producer_lengths)
#print axioms actual
#print axioms contextual
end R1Z.PV_RJN_InstalledPublishOrder

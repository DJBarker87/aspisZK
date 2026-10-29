import R1Z.PV_RJN_PublishOrder
import R1Z.PV_RunJoin_NativeCallback55
set_option autoImplicit false
namespace R1Z.PV_RJN_NativePublishOrder
open ProverRwFull PV_RunJoin_PublishSkeleton54 PV_RJN_Producers
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_NativeCallback55 (runOf)
variable [ExternalTypes] [ExternalFuns]
/-- One-step specialization to NativeCallback55's still-parametric families.
The producer obligations are front encoding size and literal layout facts. -/
theorem actual (data : Phase → PV_RunJoin_OpeningImages54.Data) (plans : Phase → Plan)
    (producer_layout : PV_RJN_Producer_Layout (runOf data plans))
    (producer_room : PV_RJN_Producer_FrontRoom (runOf data plans)) :
    PV_RunJoin_PublishContext57.PV_RunJoin_Link_PublishOrder (runOf data plans) :=
  PV_RJN_PublishOrder.actual (runOf data plans) producer_layout producer_room
#print axioms actual
end R1Z.PV_RJN_NativePublishOrder

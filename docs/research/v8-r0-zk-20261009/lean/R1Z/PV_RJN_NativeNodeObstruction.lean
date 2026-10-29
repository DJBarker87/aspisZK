import R1Z.PV_RJN_NodeObstruction
import R1Z.PV_RunJoin_NativeCallback55
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJN_NativeNodeObstruction
open ProverRwFull PV_RunJoin_PublishSkeleton54 PV_RunJoin_WeightInstalled46
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_NativeCallback55 (runOf)
/-- Well-associated successful native families cannot satisfy the unchanged
NodeAppend link. No native failure, node-byte equality or rejection is assumed. -/
theorem actual (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (data : @Phase (types base) → PV_RunJoin_OpeningImages54.Data)
    (plans : @Phase (types base) → Plan)
    (producer_layout : @PV_RJN_Producers.PV_RJN_Producer_Layout (types base)
      (selected base heap box ops) _ (@runOf (types base) data plans))
    (producer_publication : @PV_RJN_NodeObstruction.PV_RJN_Producer_Publication (types base)
      (selected base heap box ops) _ (@runOf (types base) data plans)) :
    ¬@PV_RunJoin_Link_NodeAppend (types base) (selected base heap box ops) _ (@runOf (types base) data plans) :=
  @PV_RJN_NodeObstruction.no_successful_witness (types base) (selected base heap box ops)
    _ (@runOf (types base) data plans) (PV_RJN_NodeInstalled.actual base heap box ops) producer_layout producer_publication
#print axioms actual
end R1Z.PV_RJN_NativeNodeObstruction

import R1Z.PV_RunJoin_NodeSixSequence60
import R1Z.PV_RunJoin_NodeSlotCache60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeActualSlots60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
variable [ExternalTypes] [ExternalFuns]

theorem actual (phase : Phase) (p : prover.Publication) (cc1 cc2 : host_commitment.Commitment)
    (context : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p)
    (hc1 : p.backend.c1=some cc1) (hc2 : p.backend.c2=some cc2) :
    (PV_RunJoin_ActualRun.plans phase).slots=
      PV_RunJoin_NodeSequence60.models (PV_RunJoin_NodeSixSequence60.inputs cc1 cc2 p.tree p.queries) := by
  have h (i : Fin 6) : PV_RunJoin_ActualPlanSources59.slot phase i=
      PV_RunJoin_NodePayloadModel60.model
        (PV_RunJoin_NodePayload60.payload cc1 cc2 p.tree p.queries
          (PV_RunJoin_NodeSlotCache60.batch i) (PV_RunJoin_NodeSlotCache60.tree i))
        (PV_RunJoin_NodeSlotCache60.capacity i) := by
    rw [PV_RunJoin_NodeSlotCache60.actual phase p i context]
    rw [PV_RunJoin_NodePayload60.actual p _ _ cc1 cc2 hc1 hc2]
  change [PV_RunJoin_ActualPlanSources59.slot phase 0,PV_RunJoin_ActualPlanSources59.slot phase 1,
    PV_RunJoin_ActualPlanSources59.slot phase 2,PV_RunJoin_ActualPlanSources59.slot phase 3,
    PV_RunJoin_ActualPlanSources59.slot phase 4,PV_RunJoin_ActualPlanSources59.slot phase 5]=_
  rw [h 0,h 1,h 2,h 3,h 4,h 5]
  rfl

#print axioms actual
end R1Z.PV_RunJoin_NodeActualSlots60

import R1Z.PV_RunJoin_ProducedLinks60
import R1Z.PV_RunJoin_ContextOrder60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualFrontRoom61
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
variable [ExternalTypes] [ExternalFuns]

/-- The front-room producer obligation at exactly the ActualRun families and
source-produced domain. No publication condition is inserted. -/
def FrontRoom : Prop := ∀ p : PV_RunJoin_ActualProvenance60.ActualPhase,
  (PV_RunJoin_ActualRun.plans p.val).header.length +
  (PV_RunJoin_ActualRun.plans p.val).semantic.length +
  (PV_RunJoin_ActualRun.plans p.val).claim.length ≤ Usize.max

theorem producer_iff : FrontRoom ↔
    PV_RJN_Producers.PV_RJN_Producer_FrontRoom PV_RunJoin_ActualProvenance60.runs := by
  rfl

theorem specialize (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (room : @FrontRoom (types base) (selected base heap box ops)) :
    @PV_RunJoin_PublishProduced60.PV_RunJoin_Link_PublishOrder
      (types base) (selected base heap box ops) :=
  PV_RunJoin_ProducedLinks60.publishOrder base heap box ops room

#print axioms FrontRoom
#print axioms producer_iff
#print axioms specialize
end R1Z.PV_RunJoin_ActualFrontRoom61

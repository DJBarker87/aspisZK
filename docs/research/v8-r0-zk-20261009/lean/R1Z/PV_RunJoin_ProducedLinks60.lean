import R1Z.PV_RunJoin_PublishProduced60
import R1Z.PV_RJQ_QueryRange
import R1Z.PV_RJN_InstalledPublishOrder
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ProducedLinks60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]

theorem queryRange : PV_RunJoin_PublishProduced60.PV_RunJoin_Link_QueryRange :=
  PV_RJQ_QueryRange.actual PV_RunJoin_ActualProvenance60.runs

theorem queryContext : PV_RunJoin_PublishProduced60.PV_RunJoin_Link_QueryContext := by
  intro i prepared salts publication hp hs hf
  exact ⟨prepared,salts,hp,hs,hf⟩

theorem planLayout : PV_RJN_LayoutInstalled.PV_RJN_Producer_PlanLayout PV_RunJoin_ActualProvenance60.runs := by
  intro i
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Specialization with the producer room obligation visible. It is not an
unconditional ordering discharge; malformed Phase defaults remain total. -/
theorem publishOrder (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (producer_room : @PV_RJN_Producers.PV_RJN_Producer_FrontRoom (types base) _ (@PV_RunJoin_ActualProvenance60.runs (types base) (selected base heap box ops))) :
    @PV_RunJoin_PublishProduced60.PV_RunJoin_Link_PublishOrder (types base) (selected base heap box ops) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  exact PV_RJN_ContextPublishOrder.actual _
    (PV_RJN_LayoutInstalled.actual base heap box ops _ planLayout) producer_room

#print axioms queryRange
#print axioms queryContext
#print axioms planLayout
#print axioms publishOrder
end R1Z.PV_RunJoin_ProducedLinks60

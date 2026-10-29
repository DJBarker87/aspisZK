import R1Z.PV_RunJoin_NativeResidual62
import R1Z.PV_RunJoin_ProducedLinks60
/-! The original ActualRun families and Produced predicate, at opsNative.
No link is restated and no successful-capture premise is installed as a fact. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeActual62
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeResidual62

abbrev P (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :=
  @PV_RunJoin_ActualProvenance60.ActualPhase (types base) (opsNative base heap box ops)

def runs (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    P base heap box ops → @PV_RunJoin_PublishSkeleton54.Run (types base) :=
  @PV_RunJoin_ActualProvenance60.runs (types base) (opsNative base heap box ops)

abbrev SuccessfulCapture (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :=
  Nonempty (P base heap box ops)

abbrev Links (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :=
  @PV_RunJoin_PublishProduced60.Links (types base) (opsNative base heap box ops)

theorem queryContext (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_PublishProduced60.PV_RunJoin_Link_QueryContext (types base) (opsNative base heap box ops) :=
  @PV_RunJoin_ProducedLinks60.queryContext (types base) (opsNative base heap box ops)

theorem queryRange (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_PublishProduced60.PV_RunJoin_Link_QueryRange (types base) (opsNative base heap box ops) :=
  @PV_RunJoin_ProducedLinks60.queryRange (types base) (opsNative base heap box ops)

theorem layout (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    @PV_RJN_LayoutInstalled.PV_RJN_Producer_PlanLayout _ (types base) (runs base heap box ops) :=
  @PV_RunJoin_ProducedLinks60.planLayout (types base) (opsNative base heap box ops)

#print axioms P
#print axioms runs
#print axioms SuccessfulCapture
#print axioms Links
#print axioms queryContext
#print axioms queryRange
#print axioms layout
end R1Z.PV_RunJoin_NativeActual62

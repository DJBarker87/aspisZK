import R1Z.PV_RunJoin_SourceOriginGeneric60
import R1Z.PV_RunJoin_MapErrInstalled60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualOrigin60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem actual (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box (@PV_RunJoin_MapErrInstalled60.install (types base) ops)
    ∀ p, PV_RunJoin_ActualProvenance60.Produced p → PV_RunJoin_BuildOrigin60.Origin p :=
  @PV_RunJoin_SourceOriginGeneric60.produced (types base)
    (selected base heap box (@PV_RunJoin_MapErrInstalled60.install (types base) ops))
    (PV_RunJoin_MapErrInstalled60.installed base heap box ops)

#print axioms actual
end R1Z.PV_RunJoin_ActualOrigin60

import R1Z.PV_RunJoin_CircleInstalled52
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleSource61
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

/-- Candidate source-dictionary obligation. This is not a fourth TrustItem
and is not added to any of the nine links. -/
def Source [ExternalTypes] (ops : ExternalFuns) : Prop := ∀ block row,
  ops.op259 block row = (do
    let point ← PV_RunJoin_CircleRawMap52.circle_owned block
      (PV_RunJoin_CircleNeutralSelected52.row row)
    ok (PV_RunJoin_CircleNeutralSelected52.point point))

theorem selected_iff (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @Source (types base) (selected base heap box ops) ↔ @Source (types base) ops := by
  unfold Source
  rw [PV_RunJoin_CircleInstalled52.installed_projection]

/-- This proves an explicit model installation has the operation, not that
the native caller uses this installation. -/
theorem explicit_installation [ExternalTypes] (ops : ExternalFuns) :
    Source (PV_RunJoin_CircleNeutralSelected52.selected ops) := by
  intro block row
  exact PV_RunJoin_CircleNeutralSelected52.source ops block row

#print axioms Source
#print axioms selected_iff
#print axioms explicit_installation
end R1Z.PV_RunJoin_CircleSource61

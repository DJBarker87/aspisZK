import R1Z.PV_RunJoin_CircleInstalled52
import R1Z.PV_RunJoin_CircleNeutralComplete54
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleInstalledModel54
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (block : Array U8 32#usize) (row : aspis_core.r0_transcript.CircleRow) :
    @sampler.circle_sample (types base)
      (selected base heap box (@PV_RunJoin_CircleNeutralSelected52.selected (types base) ops)) block row=(do
        let p ← PV_RunJoin_CircleFallbackPrograms54.circle block (PV_RunJoin_CircleNeutralSelected52.row row)
        ok (PV_RunJoin_CircleNeutralSelected52.point p)) := by
  rw [PV_RunJoin_CircleInstalled52.complete,PV_RunJoin_CircleNeutralComplete54.complete]
#print axioms complete
end R1Z.PV_RunJoin_CircleInstalledModel54

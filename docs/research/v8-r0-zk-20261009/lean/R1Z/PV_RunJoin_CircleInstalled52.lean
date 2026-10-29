import R1Z.PV_RunJoin_TranscriptDigest51
import R1Z.PV_RunJoin_CircleNeutralSelected52
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleInstalled52
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem candidate [ExternalTypes] (ops : ExternalFuns) :
    (ProverRwP6BodyCandidate.selected ops).op259=ops.op259 := rfl
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (b : Array U8 32#usize) (row : aspis_core.r0_transcript.CircleRow) :
    @sampler.circle_sample (types base)
      (selected base heap box (@PV_RunJoin_CircleNeutralSelected52.selected (types base) ops)) b row = (do
        let p ← PV_RunJoin_CircleRawMap52.circle_owned b (PV_RunJoin_CircleNeutralSelected52.row row)
        ok (PV_RunJoin_CircleNeutralSelected52.point p)) := by
  change (selected base heap box (@PV_RunJoin_CircleNeutralSelected52.selected (types base) ops)).op259 b row = _
  unfold selected
  rw [PV_B2_F_RawNative.preserved_259,candidate]
  exact PV_RunJoin_CircleNeutralSelected52.source ops b row

#print axioms candidate
#print axioms complete
end R1Z.PV_RunJoin_CircleInstalled52

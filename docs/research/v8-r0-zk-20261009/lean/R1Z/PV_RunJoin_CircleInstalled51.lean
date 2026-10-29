import R1Z.PV_RunJoin_TranscriptDigest51
import R1Z.PV_AL_CircleSelected
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleInstalled51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46

theorem candidate [ExternalTypes] (ops : ExternalFuns) :
    (ProverRwP6BodyCandidate.selected ops).op259=ops.op259 := rfl
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (b : Array U8 32#usize) (row : aspis_core.r0_transcript.CircleRow) :
    @sampler.circle_sample (types base)
      (selected base heap box (@PV_AL_CircleSelected.selected (types base) ops)) b row=(do
        let point ← PV_AL_CircleNative.nativeCircle b (PV_AL_CircleCarriers.encodeRow row)
        ok (PV_AL_CircleCarriers.decodePoint point)) := by
  change (selected base heap box (@PV_AL_CircleSelected.selected (types base) ops)).op259 b row=_
  unfold selected
  rw [PV_B2_F_RawNative.preserved_259,candidate]
  exact @PV_AL_CircleSelected.native_source (types base) ops b row
#print axioms candidate
#print axioms complete
end R1Z.PV_RunJoin_CircleInstalled51

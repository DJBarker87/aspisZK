import R1Z.PV_RunJoin_TranscriptDigest51
import R1Z.ProverRwFullSampler
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticSamplerField51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46

theorem candidate [ExternalTypes] (ops : ExternalFuns) :
    (ProverRwP6BodyCandidate.selected ops).op248=ProverRwFullSampler.selected := rfl
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem installed (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) :
    (selected base heap box ops).op248=ProverRwFullSampler.selected := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_248]
  exact @candidate (types base) ops
#print axioms candidate
#print axioms installed
end R1Z.PV_RunJoin_SemanticSamplerField51

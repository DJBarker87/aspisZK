import R1Z.PV_RunJoin_TranscriptDigest51
import R1Z.ProverRwOuterTag
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TranscriptTag51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46

theorem candidate [ExternalTypes] (ops : ExternalFuns) (v : transport.Variant) :
    (ProverRwP6BodyCandidate.selected ops).op234 v=ok (ProverRwOuterTag.byte v) := by
  cases v <;> rfl
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem installed (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (v : transport.Variant) :
    (selected base heap box ops).op234 v=ok (ProverRwOuterTag.byte v) := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_234]
  exact @candidate (types base) ops v
#print axioms candidate
#print axioms installed
end R1Z.PV_RunJoin_TranscriptTag51

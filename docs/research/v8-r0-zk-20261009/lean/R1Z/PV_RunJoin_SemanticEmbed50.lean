import R1Z.PV_RunJoin_SemanticScalar50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticEmbed50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitPrimitive47 ProverCommitSubfieldOps47

theorem candidate [ExternalTypes] (ops : ExternalFuns) :
    (ProverRwP6BodyCandidate.selected ops).op45=ProverRwDictionaryTower.wEmbed := rfl
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem field (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op45 (types base) (selected base heap box ops)=ProverRwDictionaryTower.wEmbed := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_45]
  exact @candidate (types base) ops

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (q : aspis_core.field.QM31) :
    @aspis_core.field.wide_exact.WideExact.from_qm31 (types base) (selected base heap box ops) q=
      ok (ProverRwDictionaryTower.fromW
        (ProverCommitNativeOps47.embedded (PV_RunJoin_SemanticScalar50.raw q))) := by
  change @ExternalFuns.op45 (types base) (selected base heap box ops) q=_
  rw [field]
  rw [←PV_RunJoin_SemanticScalar50.source q]
  rfl
#print axioms candidate
#print axioms field
#print axioms complete
end R1Z.PV_RunJoin_SemanticEmbed50

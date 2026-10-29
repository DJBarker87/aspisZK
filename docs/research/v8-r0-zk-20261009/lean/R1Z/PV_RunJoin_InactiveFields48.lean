import R1Z.PV_RunJoin_WeightInstalled46
import R1Z.ProverRwDictionaryWideQM
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InactiveFields48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverRwDictionaryTower (fromW toW toQ)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem candidate_zero [ExternalTypes] (ops : ExternalFuns) :
    (ProverRwP6BodyCandidate.selected ops).op42=
      ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) := rfl

theorem candidate_add [ExternalTypes] (ops : ExternalFuns) :
    (ProverRwP6BodyCandidate.selected ops).op46=ProverRwDictionaryTower.wAdd := rfl

theorem candidate_mul [ExternalTypes] (ops : ExternalFuns) :
    (ProverRwP6BodyCandidate.selected ops).op48=ProverRwDictionaryWideQM.mul := rfl

theorem zero (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op42 (types base) (selected base heap box ops)=
      ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_42]
  exact @candidate_zero (types base) ops

theorem add (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op46 (types base) (selected base heap box ops)=ProverRwDictionaryTower.wAdd := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_46]
  exact @candidate_add (types base) ops

theorem mul (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op48 (types base) (selected base heap box ops)=ProverRwDictionaryWideQM.mul := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_48]
  exact @candidate_mul (types base) ops
#print axioms candidate_zero
#print axioms candidate_add
#print axioms candidate_mul
#print axioms zero
#print axioms add
#print axioms mul
end R1Z.PV_RunJoin_InactiveFields48

import R1Z.PV_RunJoin_WeightInstalled46
import R1Z.ProverRwDictionaryScalar
import R1Z.PV_RunJoin_WeightMap46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncoderFields49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverRwDictionaryTower (fromW toW native_w_roundtrip)
open PV_RunJoin_WeightMap46 (mapResult)
abbrev S := AspisR1ProducerRelease47.field.wide_exact.WideExact
abbrev W := aspis_core.field.wide_exact.WideExact

theorem candidate_zero [ExternalTypes] (ops : ExternalFuns) :
  (ProverRwP6BodyCandidate.selected ops).op88=ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) := rfl
theorem candidate_one [ExternalTypes] (ops : ExternalFuns) :
  (ProverRwP6BodyCandidate.selected ops).op91=ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE) := rfl
theorem candidate_mul [ExternalTypes] (ops : ExternalFuns) :
  (ProverRwP6BodyCandidate.selected ops).op103=ProverRwDictionaryTower.wMul := rfl
theorem candidate_add [ExternalTypes] (ops : ExternalFuns) :
  (ProverRwP6BodyCandidate.selected ops).op94=ProverRwDictionaryTower.wAdd := rfl
theorem candidate_sub [ExternalTypes] (ops : ExternalFuns) :
  (ProverRwP6BodyCandidate.selected ops).op97=(fun a b => ProverRwDictionaryTower.mapResult fromW
    (AspisR1ProducerRelease47.field.wide_exact.WideExact.sub (toW a) (toW b))) := rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem zero (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) :
  (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField (types base) (selected base heap box ops)).ZERO=
    ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) := by
  change @ExternalFuns.op88 (types base) (selected base heap box ops)=_
  unfold selected
  rw [PV_B2_F_RawNative.preserved_88]
  exact @candidate_zero (types base) ops

theorem one (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) :
  (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField (types base) (selected base heap box ops)).ONE=
    ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE) := by
  change @ExternalFuns.op91 (types base) (selected base heap box ops)=_
  unfold selected
  rw [PV_B2_F_RawNative.preserved_91]
  exact @candidate_one (types base) ops

#print axioms candidate_zero
#print axioms candidate_one
#print axioms candidate_mul
#print axioms candidate_add
#print axioms candidate_sub
#print axioms zero
#print axioms one
end R1Z.PV_RunJoin_EncoderFields49

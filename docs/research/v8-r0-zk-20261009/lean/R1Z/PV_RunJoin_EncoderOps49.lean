import R1Z.PV_RunJoin_EncoderFields49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncoderOps49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverRwDictionaryTower (fromW toW native_w_roundtrip)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderFields49 (S W)

theorem maps {A B : Type} (f : A → B) (r : Result A) :
    ProverRwDictionaryTower.mapResult f r=mapResult f r := by cases r <;> rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem mul_field (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) :
  (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField (types base) (selected base heap box ops)).mul=
    ProverRwDictionaryTower.wMul := by
  change @ExternalFuns.op103 (types base) (selected base heap box ops)=_
  unfold selected
  rw [PV_B2_F_RawNative.preserved_103]
  exact @PV_RunJoin_EncoderFields49.candidate_mul (types base) ops

theorem add_field (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) :
  (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField (types base) (selected base heap box ops)).add=
    ProverRwDictionaryTower.wAdd := by
  change @ExternalFuns.op94 (types base) (selected base heap box ops)=_
  unfold selected
  rw [PV_B2_F_RawNative.preserved_94]
  exact @PV_RunJoin_EncoderFields49.candidate_add (types base) ops

theorem sub_field (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) :
  (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField (types base) (selected base heap box ops)).sub=
    (fun a b => ProverRwDictionaryTower.mapResult fromW
      (AspisR1ProducerRelease47.field.wide_exact.WideExact.sub (toW a) (toW b))) := by
  change @ExternalFuns.op97 (types base) (selected base heap box ops)=_
  unfold selected
  rw [PV_B2_F_RawNative.preserved_97]
  exact @PV_RunJoin_EncoderFields49.candidate_sub (types base) ops

attribute [local irreducible] selected PV_B2_F_RawNative.selected

theorem mul (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) (a b : S) :
  (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField (types base) (selected base heap box ops)).mul (fromW a) (fromW b)=
    mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b) := by
  rw [mul_field base heap box ops,ProverRwDictionaryTower.wMul,native_w_roundtrip,native_w_roundtrip,maps]

theorem add (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) (a b : S) :
  (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField (types base) (selected base heap box ops)).add (fromW a) (fromW b)=
    mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.add a b) := by
  rw [add_field base heap box ops,ProverRwDictionaryTower.wAdd,native_w_roundtrip,native_w_roundtrip,maps]

theorem sub (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) (a b : S) :
  (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField (types base) (selected base heap box ops)).sub (fromW a) (fromW b)=
    mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.sub a b) := by
  rw [sub_field base heap box ops]
  dsimp only
  rw [native_w_roundtrip,native_w_roundtrip,maps]
#print axioms maps
#print axioms mul_field
#print axioms add_field
#print axioms sub_field
#print axioms mul
#print axioms add
#print axioms sub
end R1Z.PV_RunJoin_EncoderOps49

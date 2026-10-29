import R1Z.PV_RunJoin_BatchFields48
import R1Z.PV_RunJoin_ResultMap50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaOps50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverRwDictionaryTower (fromW toW)
open PV_RunJoin_WeightMap46 (mapResult)
abbrev S := AspisR1ProducerRelease47.field.wide_exact.WideExact
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem mul (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) (a b : S) :
    @aspis_core.field.wide_exact.WideExact.mul (types base) (selected base heap box ops) (fromW a) (fromW b)=
      mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b) := by
  change @ExternalFuns.op47 (types base) (selected base heap box ops) _ _=_
  rw [PV_RunJoin_BatchFields48.mul base heap box ops,PV_RunJoin_BatchFields48.candidate_mul]
  simp only [ProverRwDictionaryTower.wMul,ProverRwDictionaryTower.native_w_roundtrip]

theorem add (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) (a b : S) :
    @aspis_core.field.wide_exact.WideExact.add (types base) (selected base heap box ops) (fromW a) (fromW b)=
      mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.add a b) := by
  change @ExternalFuns.op46 (types base) (selected base heap box ops) _ _=_
  rw [PV_RunJoin_InactiveFields48.add base heap box ops]
  simp only [ProverRwDictionaryTower.wAdd,ProverRwDictionaryTower.native_w_roundtrip]
#print axioms mul
#print axioms add
end R1Z.PV_RunJoin_GammaOps50

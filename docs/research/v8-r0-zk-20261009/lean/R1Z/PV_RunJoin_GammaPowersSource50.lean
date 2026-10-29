import R1Z.PV_RunJoin_EncoderGammaFields49
import R1Z.ProverRwP6PowersGammaSource
import R1Z.PV_RunJoin_ResultMap50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaPowersSource50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW)
open PV_RunJoin_WeightMap46 (mapResult)
abbrev S := ProverCommitWideOps48.Source
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) (g : S) :
    @weights.powers (types base)
      (selected base heap box (@PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)))
      29#usize (fromW g)=mapResult (amap fromW) (AspisR1ProducerRelease47.gamma g) := by
  letI : ExternalTypes := types base
  change @ExternalFuns.op254 (types base) (selected base heap box _) 29#usize (fromW g)=_
  rw [PV_RunJoin_EncoderGammaFields49.powers base heap box]
  change ProverRwP6PowersInstall.powers ops 29#usize (fromW g)=_
  have source := @ProverRwP6PowersGammaSource.gamma (types base) ops (fromW g)
  change ProverRwP6PowersInstall.powers ops 29#usize (fromW g)=_ at source
  rw [source]
  change ProverRwP6ResultMap.map (ProverRwP6ArrayMap.map fromW)
    (AspisR1ProducerRelease47.gamma (ProverRwDictionaryTower.toW (fromW g)))=_
  rw [ProverRwDictionaryTower.native_w_roundtrip]
  rfl
#print axioms complete
end R1Z.PV_RunJoin_GammaPowersSource50

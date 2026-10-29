import R1Z.PV_RunJoin_GammaVectorActual50
import R1Z.PV_RunJoin_GammaPowersSource50
import R1Z.ProverCommitGammaOutput53
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaBatchActual50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_GammaSourceCell50 (Columns)
abbrev S := ProverCommitWideOps48.Source
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (c : Columns) (g : S) :
    let incoming := @PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)
    @prover.opening_batch (types base) (selected base heap box incoming)
      (Array.to_slice (amap (amap fromW) c)) (fromW g)=
        mapResult (PV_RunJoin_PrefixFold50.image fromW) (ProverCommitGammaOutput53.run c g) := by
  dsimp only
  let incoming := @PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)
  unfold prover.opening_batch ProverCommitGammaOutput53.run
  rw [PV_RunJoin_GammaPowersSource50.complete base heap box ops g]
  symm
  apply PV_RunJoin_WeightMap46.map_bind (amap fromW) (PV_RunJoin_PrefixFold50.image fromW)
  intro powers
  exact (PV_RunJoin_GammaVectorActual50.complete base heap box incoming c powers).symm
#print axioms complete
end R1Z.PV_RunJoin_GammaBatchActual50

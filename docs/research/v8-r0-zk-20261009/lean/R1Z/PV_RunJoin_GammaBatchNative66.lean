import R1Z.PV_RunJoin_GammaBatchActual50
import R1Z.PV_RunJoin_BatchCongruence48
import R1Z.PV_RunJoin_NativePowerBinding66
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_GammaBatchNative66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW toW)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_GammaSourceCell50 (Columns)
abbrev S := ProverCommitWideOps48.Source
abbrev W := aspis_core.field.wide_exact.WideExact

theorem frame [t : ExternalTypes] (left right : ExternalFuns)
    (hz : left.op42=right.op42) (hm : left.op47=right.op47) (ha : left.op46=right.op46)
    (coefficients : Slice (Array W 1024#usize)) (g : W)
    (hp : @weights.powers t left 29#usize g=@weights.powers t right 29#usize g) :
    @prover.opening_batch t left coefficients g=@prover.opening_batch t right coefficients g := by
  rw [@PV_RunJoin_BatchThread44.caller t left,@PV_RunJoin_BatchThread44.caller t right,hp]
  simp only [PV_RunJoin_BatchCongruence48.phase left right hz hm ha]

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (powers : ∀ x, @ExternalFuns.op254 (types base) ops 29#usize x=
      mapResult (amap fromW) (AspisR1ProducerRelease47.gamma (toW x))) (c : Columns) (g : S) :
    @prover.opening_batch (types base) (selected base heap box ops)
      (Array.to_slice (amap (amap fromW) c)) (fromW g)=
        mapResult (PV_RunJoin_PrefixFold50.image fromW) (ProverCommitGammaOutput53.run c g) := by
  letI : ExternalTypes := types base
  let incoming := @PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)
  have hz := (PV_RunJoin_InactiveFields48.zero base heap box ops).trans
    (PV_RunJoin_InactiveFields48.zero base heap box incoming).symm
  have ha := (PV_RunJoin_InactiveFields48.add base heap box ops).trans
    (PV_RunJoin_InactiveFields48.add base heap box incoming).symm
  have hm := ((PV_RunJoin_BatchFields48.mul base heap box ops).trans
    (@PV_RunJoin_BatchFields48.candidate_mul (types base) ops)).trans
      ((PV_RunJoin_BatchFields48.mul base heap box incoming).trans
        (@PV_RunJoin_BatchFields48.candidate_mul (types base) incoming)).symm
  have hp : @weights.powers (types base) (selected base heap box ops) 29#usize (fromW g)=
      @weights.powers (types base) (selected base heap box incoming) 29#usize (fromW g) := by
    change @ExternalFuns.op254 (types base) (selected base heap box ops) _ _=_
    rw [PV_RunJoin_EncoderGammaFields49.powers base heap box ops,powers,
      ProverRwDictionaryTower.native_w_roundtrip]
    exact (PV_RunJoin_GammaPowersSource50.complete base heap box ops g).symm
  rw [frame _ _ hz hm ha _ _ hp]
  exact PV_RunJoin_GammaBatchActual50.complete base heap box ops c g
#print axioms frame
#print axioms complete
end R1Z.PV_RunJoin_GammaBatchNative66

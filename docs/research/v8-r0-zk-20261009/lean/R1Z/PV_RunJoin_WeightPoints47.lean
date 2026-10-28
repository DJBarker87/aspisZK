import R1Z.PV_RunJoin_WeightPointsStage947
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPoints47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K amap)
open PV_RunJoin_WeightKernel46 (toQ)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

theorem complete (z : Array K 10#usize) :
    AspisR1ProducerRelease47.points.all (amap toQ z)=
      mapResult (amap (amap toQ)) (PV_B2_C_WeightsNative.host_weights.state_only_statement_points z) := by
  rw [PV_RunJoin_WeightPointsStages47.source,PV_RunJoin_WeightPointsStage947.complete]
  unfold PV_RunJoin_WeightPointsFinish47.result AspisR1ProducerRelease47.points.all
  rw [PV_RunJoin_WeightKernel46.one,PV_RunJoin_WeightSuccessor46.complete z 10 z 10#u8 _ rfl]
  symm
  apply map_bind (amap toQ) (amap (amap toQ))
  intro out
  rw [PV_RunJoin_WeightAbsorption46.complete]
  apply map_bind (amap toQ) (amap (amap toQ))
  intro absorbed
  rfl
#print axioms complete
end R1Z.PV_RunJoin_WeightPoints47

import R1Z.PV_RunJoin_WeightPointsStage847
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointsStage947
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightPointsStages47
open PV_RunJoin_WeightPointsFinish47 (result)
open PV_RunJoin_WeightPointCounters47

theorem complete (z out : Point) (carry bit7 : PV_B2_F_ConstructorCarrier.K) :
    stage9 z out carry bit7=
      result z (PV_RunJoin_WeightSuccessor46.remaining z 10 out 10#u8 carry) := by
  rw [stage9,result,PV_RunJoin_WeightSuccessor46.remaining]
  simp only [sub10,cast9,bind_assoc]
  simp only [PV_RunJoin_WeightPointsStage847.complete,result,bind_assoc]
#print axioms complete
end R1Z.PV_RunJoin_WeightPointsStage947

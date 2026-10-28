import R1Z.PV_RunJoin_WeightPointsStage747
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointsStage847
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightPointsStages47
open PV_RunJoin_WeightPointsFinish47 (result)
open PV_RunJoin_WeightPointCounters47

theorem complete (z out : Point) (carry bit7 : PV_B2_F_ConstructorCarrier.K) :
    stage8 z out carry bit7=
      result z (PV_RunJoin_WeightSuccessor46.remaining z 9 out 9#u8 carry) := by
  rw [stage8,result,PV_RunJoin_WeightSuccessor46.remaining]
  simp only [sub9,cast8,bind_assoc]
  simp only [PV_RunJoin_WeightPointsStage747.complete,result,bind_assoc]
#print axioms complete
end R1Z.PV_RunJoin_WeightPointsStage847

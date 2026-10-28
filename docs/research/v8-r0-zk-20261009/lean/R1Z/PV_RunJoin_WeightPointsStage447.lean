import R1Z.PV_RunJoin_WeightPointsStage347
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointsStage447
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightPointsStages47
open PV_RunJoin_WeightPointsFinish47 (result)
open PV_RunJoin_WeightPointCounters47

theorem complete (z out : Point) (carry bit7 : PV_B2_F_ConstructorCarrier.K)
    (h7 : Array.index_usize z 7#usize=ok bit7) :
    stage4 z out carry bit7=
      result z (PV_RunJoin_WeightSuccessor46.remaining z 5 out 5#u8 carry) := by
  rw [stage4,result,PV_RunJoin_WeightSuccessor46.remaining]
  simp only [sub5,cast4,bind_assoc]
  simp only [PV_RunJoin_WeightPointsStage347.complete z _ _ bit7 h7,result,bind_assoc]
#print axioms complete
end R1Z.PV_RunJoin_WeightPointsStage447

import R1Z.PV_RunJoin_WeightPointsStage147
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointsStage247
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightPointsStages47
open PV_RunJoin_WeightPointsFinish47 (result)
open PV_RunJoin_WeightPointCounters47

theorem complete (z out : Point) (carry bit7 : PV_B2_F_ConstructorCarrier.K)
    (h7 : Array.index_usize z 7#usize=ok bit7) :
    stage2 z out carry bit7=
      result z (PV_RunJoin_WeightSuccessor46.remaining z 3 out 3#u8 carry) := by
  rw [stage2,result,PV_RunJoin_WeightSuccessor46.remaining]
  simp only [sub3,cast2,bind_assoc]
  simp only [PV_RunJoin_WeightPointsStage147.complete z _ _ bit7 h7,result,bind_assoc]
#print axioms complete
end R1Z.PV_RunJoin_WeightPointsStage247

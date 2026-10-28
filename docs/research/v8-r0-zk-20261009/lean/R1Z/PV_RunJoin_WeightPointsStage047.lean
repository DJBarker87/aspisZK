import R1Z.PV_RunJoin_WeightPointsFinish47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointsStage047
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightPointsStages47
open PV_RunJoin_WeightPointsFinish47 (result)
open PV_RunJoin_WeightPointCounters47

theorem complete (z out : Point) (carry bit7 : PV_B2_F_ConstructorCarrier.K)
    (h7 : Array.index_usize z 7#usize=ok bit7) :
    stage0 z out carry bit7=
      result z (PV_RunJoin_WeightSuccessor46.remaining z 1 out 1#u8 carry) := by
  rw [stage0,result,PV_RunJoin_WeightSuccessor46.remaining]
  simp only [sub1,cast0,bind_assoc,PV_RunJoin_WeightSuccessor46.remaining,bind_tc_ok]
  simp only [PV_RunJoin_WeightPointsFinish47.complete z _ bit7 h7,result,bind_tc_ok]
#print axioms complete
end R1Z.PV_RunJoin_WeightPointsStage047

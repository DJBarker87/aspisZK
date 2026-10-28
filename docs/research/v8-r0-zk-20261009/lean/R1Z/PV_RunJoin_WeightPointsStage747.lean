import R1Z.PV_RunJoin_WeightPointsStage647
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointsStage747
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightPointsStages47
open PV_RunJoin_WeightPointsFinish47 (result)
open PV_RunJoin_WeightPointCounters47

theorem complete (z out : Point) (carry bit7 : PV_B2_F_ConstructorCarrier.K) :
    stage7 z out carry bit7=
      result z (PV_RunJoin_WeightSuccessor46.remaining z 8 out 8#u8 carry) := by
  rw [stage7,result,PV_RunJoin_WeightSuccessor46.remaining]
  simp only [sub8,cast7,bind_assoc]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro bit h7
  simp only [PV_RunJoin_WeightPointsStage647.complete z _ _ bit h7,result,bind_assoc]
#print axioms complete
end R1Z.PV_RunJoin_WeightPointsStage747

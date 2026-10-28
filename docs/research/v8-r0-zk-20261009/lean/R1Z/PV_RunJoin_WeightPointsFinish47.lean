import R1Z.PV_RunJoin_WeightPointsStages47
import R1Z.PV_RunJoin_WeightPointCounters47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointsFinish47
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightPointsStages47
open PV_B2_C_WeightsNative

def result (z : Point) (r : Result Point) : Result Points := do
  let out ← r
  let absorbed ← PV_RunJoin_WeightAbsorption46.run z
  ok (Array.make 3#usize [z,out,absorbed])

theorem complete (z out : Point) (bit7 : PV_B2_F_ConstructorCarrier.K)
    (h7 : Array.index_usize z 7#usize=ok bit7) :
    finish z out bit7=result z (ok out) := by
  simp only [finish,result,PV_RunJoin_WeightAbsorption46.run,h7,bind_tc_ok,bind_assoc]
#print axioms complete
end R1Z.PV_RunJoin_WeightPointsFinish47

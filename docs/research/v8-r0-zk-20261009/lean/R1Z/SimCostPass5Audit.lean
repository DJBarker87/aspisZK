import R1Z.SimCostWide5
import R1Z.SimCostCollect5
import R1Z.SimCostFormula5
import R1Z.SimCostRetry5
import R1Z.PrivacyR1HeadlineV2SimProto
import R1Z.ProverCommitDeployedFuel22

/-! Focused cached assembly audit, not a frozen-manifest release replay.
No efficiency premise is removed by importing independent local results. -/
#print axioms R1Z.SimCostWide5.add_erase
#print axioms R1Z.SimCostWide5.add_cost
#print axioms R1Z.SimCostWide5.mul_erase
#print axioms R1Z.SimCostWide5.mul_cost
#print axioms R1Z.SimCostWide5.power_erase
#print axioms R1Z.SimCostWide5.power_bound
#print axioms R1Z.SimCostWide5.inverse_exponent_bound
#print axioms R1Z.SimCostWide5.inverse_power
#print axioms R1Z.SimCostWide5.inv_erase
#print axioms R1Z.SimCostWide5.inv_bound
#print axioms R1Z.SimCostCollect5.collect_erase
#print axioms R1Z.SimCostCollect5.collect_bound
#print axioms R1Z.SimCostCollect5.collect2_erase
#print axioms R1Z.SimCostCollect5.collect2_bound
#print axioms R1Z.SimCostCollect5.collect3_erase
#print axioms R1Z.SimCostCollect5.collect3_bound
#print axioms R1Z.SimCostFormula5.arrayAdd_erase
#print axioms R1Z.SimCostFormula5.arrayAdd_bound
#print axioms R1Z.SimCostFormula5.payloadEquiv
#print axioms R1Z.SimCostFormula5.payload_nat_card
#print axioms R1Z.SimCostFormula5.payload_card
#print axioms R1Z.SimCostFormula5.full_array_add_bound
#print axioms R1Z.SimCostRetry5.zeroBytes_erase
#print axioms R1Z.SimCostRetry5.zeroBytes_cost
#print axioms R1Z.SimCostRetry5.zeroWord_erase
#print axioms R1Z.SimCostRetry5.zeroWord_cost
#print axioms R1Z.SimCostRetry5.search_none
#print axioms R1Z.SimCostRetry5.search_bound
#print axioms R1Z.SimCostRetry5.allSearch_bound
#print axioms R1Z.SimCostRetry5.exhaustion_mass
#print axioms R1Z.SimCostWide5.add
#print axioms R1Z.SimCostWide5.mul
#print axioms R1Z.SimCostWide5.inv
#print axioms R1Z.SimCostFormula5.arrayAdd
#print axioms R1Z.SimCostIdeal.Preparation
#print axioms R1Z.PrivacyR1HeadlineV2SimProto.privacy_headline_v2_sim_proto
#print axioms R1Z.ProverCommitDeployedFuel22.RustProverRefinement
#print axioms R1Z.ProverCommitFuelJoin22.RunJoin

#print R1Z.ProverCommitFuelJoin22.RunJoin

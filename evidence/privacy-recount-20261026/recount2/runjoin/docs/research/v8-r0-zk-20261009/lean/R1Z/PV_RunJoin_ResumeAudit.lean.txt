import R1Z.PV_RunJoin_WorldAudit
import R1Z.PV_RunJoin_CanonicalFixtures

/-! Final focused cached audit of this resume. Neither a deployed source
certificate nor a full frozen-manifest replay is supplied. -/
#print axioms R1Z.PV_RunJoin_WorldTotal.cap8_total
#print axioms R1Z.PV_RunJoin_FixtureRecords.spend
#print axioms R1Z.PV_RunJoin_SpendRelationMap.rspend_map_iff
#print axioms R1Z.PV_RunJoin_FixtureFibres.lift_spendPlus
#print axioms R1Z.PV_RunJoin_TransferSentinel.value
#print axioms R1Z.PV_RunJoin_TransferSentinel.nonzero
#print axioms R1Z.PV_RunJoin_CanonicalFixtures.transfer
#print axioms R1Z.PV_RunJoin_CanonicalFixtures.withdrawal
#print axioms R1Z.PV_RunJoin_CanonicalFixtures.predecessor_premises
#print axioms R1Z.PV_RunJoin_CanonicalFixtures.fibres
#print axioms R1Z.PV_RunJoin_CanonicalFixtures.mathematical_fibres
#print axioms R1Z.PV_RunJoin_AbstractEndpoint.privacy_headline_from_premises
#check @R1Z.PV_RunJoin_CanonicalFixtures.Association.transfer_public_V047
#check @R1Z.PV_RunJoin_CanonicalFixtures.Association.withdrawal_public_V047
#check @R1Z.PV_RunJoin_AbstractEndpoint.PV_RunJoin_Premises.uniform_V037
#check @R1Z.PV_RunJoin_AbstractEndpoint.PV_RunJoin_Premises.disclosed_V038
#check @R1Z.PV_RunJoin_AbstractEndpoint.PV_RunJoin_Premises.observerOracle_V038

import R1Z.PV_RunJoin_TrustItems
import R1Z.PV_RunJoin_TrustEndpoint
set_option pp.explicit true
#print R1Z.PV_RunJoin_TrustBoundary.Observation
#print R1Z.PV_RunJoin_TrustBoundary.Data
#print R1Z.PV_RunJoin_TrustItems
#print R1Z.PV_RunJoin_TrustEndpoint.ProofObligations
#check @R1Z.PV_RunJoin_TrustEndpoint.complete_view
#print axioms R1Z.PV_RunJoin_TrustEndpoint.complete_view
#check @R1Z.PV_RunJoin_TrustEndpoint.toPremises
#print axioms R1Z.PV_RunJoin_TrustEndpoint.toPremises
#check @R1Z.PV_RunJoin_TrustEndpoint.privacy_headline_deployed_candidate
#print axioms R1Z.PV_RunJoin_TrustEndpoint.privacy_headline_deployed_candidate

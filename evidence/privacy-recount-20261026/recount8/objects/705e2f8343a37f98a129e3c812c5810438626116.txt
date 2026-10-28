import R1Z.PV_RunJoin_CausalHeadline
import R1Z.PV_RunJoin_SelectedSourceCore
import R1Z.PV_RunJoin_ExternalRefinement
import R1Z.PV_RunJoin_RootLoop
import R1Z.PV_RunJoin_SourceSbox
/-! Focused audit of this round's accepted sources. This is not the complete
release manifest or an installed deployed-fixture non-vacuity certificate. -/
#print R1Z.PV_RunJoin_TrustItems
#print R1Z.PV_RunJoin_TrustEndpoint.ProofObligations
#print R1Z.PV_RunJoin_TrustLedger.RemainingProofs
#check @R1Z.PV_RunJoin_CausalHeadline.privacy_headline_deployed_candidate
#print axioms R1Z.PV_RunJoin_TrustEndpoint.privacy_headline_deployed_candidate
#print axioms R1Z.PV_RunJoin_TrustLedger.privacy_headline_deployed_candidate
#print axioms R1Z.PV_RunJoin_CausalTrustLedger.initial_and_causal
#print axioms R1Z.PV_RunJoin_CausalHeadline.proofs
#print axioms R1Z.PV_RunJoin_CausalHeadline.privacy_headline_deployed_candidate
#print axioms R1Z.PV_RunJoin_SelectedSourceCore.words_and_public
#print axioms R1Z.PV_RunJoin_SourceArithmeticLift.reduce
#print axioms R1Z.PV_RunJoin_SourceScalar.forest_mul
#print axioms R1Z.PV_RunJoin_ExternalRefinement.owned
#print axioms R1Z.PV_RunJoin_ExternalRefinement.dictionary
#print axioms R1Z.PV_RunJoin_RootLoop.roots

#print axioms R1Z.PV_RunJoin_SourceSbox.pow5

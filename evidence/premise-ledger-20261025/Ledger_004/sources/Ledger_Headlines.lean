import Port1_CanonicalHeadline
import OraclePortHeadlineFrozen2PerAttempt
set_option pp.all false
set_option pp.explicit false
set_option pp.fullNames true
set_option pp.universes false
set_option format.width 120
#check @AspisR1.OraclePortHeadlineFrozen2PerAttempt.final_soundness
#print axioms AspisR1.OraclePortHeadlineFrozen2PerAttempt.final_soundness
#check @AspisR1.Port1_CanonicalHeadline.final_soundness
#print axioms AspisR1.Port1_CanonicalHeadline.final_soundness
#check @AspisR1.Port1_CanonicalHeadline.runtime_transport
#print axioms AspisR1.Port1_CanonicalHeadline.runtime_transport
#check @AspisR1.Port1_CanonicalJoin.two_pass
#print axioms AspisR1.Port1_CanonicalJoin.two_pass
#print AspisR1.OraclePortFrozen2Join.AcceptedRunJoin
#print AspisR1.OraclePortFrozen2Join.AcceptedVerifierJoin
#print AspisR1.Port1_CanonicalJoin.AcceptedRunJoin
#print AspisR1.Port1_CanonicalJoin.AcceptedVerifierJoin
#print AspisR1.Port1_StoredCarrier.Carried
#print AspisR1.Port1_StoredCarrier.Physical
#print AspisR1.OraclePortRuntimeBindingC7.StoredCarrierBinding
#print AspisR1.OraclePortHeadlineFrozen2PerAttempt.Claims

import CPP_Endpoint
import CPP_ProtectedObservation
import CPP_ResultOrder
import CPP_BankBinding
import CPP_AtomicDriver
import CPP_AtomicClean
import CPP_BankCacheGap
import CPP_CommitGeometry
set_option pp.proofs false
set_option pp.depth 10000

/- Display-only audit. The historical root remains unchanged. Compare the
actual quantified statements and both old/new continuation definitions. -/
#check AspisR1.T2R_Top.deployed
#check AspisR1.CPP_Endpoint.deployed
#check AspisR1.CPP_ResultOrder.original
#check AspisR1.CPP_ProtectedObservation.checkpoint
#print AspisR1.T2R_Acceptance.Facts
#print AspisR1.CPP_Acceptance.Facts
#print AspisR1.T2R_CallerSource.Outcome
#print AspisR1.CPP_CallerSource.Outcome
#print AspisR1.CPP_ProtectedResult.Outcome
#check AspisR1.CPP_AtomicJoint.one_loss
#check AspisR1.CPP_BankBinding.binding
#check AspisR1.CPP_BankCacheGap.marker_not_sufficient

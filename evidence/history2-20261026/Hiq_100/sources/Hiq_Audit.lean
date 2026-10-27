import Hiq_CanonicalAccountDriver
import Hiq_NativeVersion
import Hiq_AuthenticatedPrograms
import Hiq_DispatchOracle
import Hiq_PoolGuards
import Hiq_AccountClean
import Hiq_CommonEvent
import Hiq_AccountLoss
import Hiq_StoredTransport
import Hiq_RuntimeScope
import Hiq_RuntimeNonvacuity
import Hiq_ExactMargin
set_option autoImplicit false

#print axioms AspisR1.Hiq_CanonicalAccountDriver.accepted
#print axioms AspisR1.Hiq_NativeVersion.version
#print axioms AspisR1.Hiq_FirstShape.source
#print axioms AspisR1.Hiq_AuthenticatedPrograms.inputs
#print axioms AspisR1.Hiq_DispatchRelease.source
#print axioms AspisR1.Hiq_DispatchRelease.lifecycle_irrelevant
#print axioms AspisR1.Hiq_DispatchOracle.source
#print axioms AspisR1.Hiq_PoolGuards.account_iff
#print axioms AspisR1.Hiq_PoolGuards.owned_iff
#print axioms AspisR1.Hiq_RuntimeNonvacuity.nonempty
#print axioms AspisR1.Hiq_AccountClean.exists_clean
#print axioms AspisR1.Hiq_CommonEvent.union_subset
#print axioms AspisR1.Hiq_AccountLoss.one_loss
#print axioms AspisR1.Hiq_BindingFailure.mass
#print axioms AspisR1.Hiq_StoredTransport.transport
#print axioms AspisR1.Hiq_RuntimeScope.carried_insufficient
#print axioms AspisR1.Hiq_ExactMargin.new_term
#print axioms AspisR1.Hiq_ExactMargin.exact_margin
#print axioms AspisR1.Hiq_ExactMargin.positive_margin

set_option pp.proofs false in
#print AspisR1.Hiq_CanonicalAccountDriver.accepted
set_option pp.proofs false in
#print AspisR1.Hiq_CommonEvent.union_subset
set_option pp.proofs false in
#print AspisR1.Hiq_AccountLoss.one_loss
set_option pp.proofs false in
#print AspisR1.Hiq_StoredTransport.transport
set_option pp.proofs false in
#print AspisR1.Hiq_RuntimeScope.carried_insufficient

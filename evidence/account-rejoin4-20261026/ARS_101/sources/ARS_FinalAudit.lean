import ARS_AccountDomination
import ARS_AccountReplay
import ARS_AdaptiveCost
import ARS_BudgetFromTotal
import ARS_Carrier
import ARS_Chronology
import ARS_ConditionalMass
import ARS_ConditionalNumeric
import ARS_CostObstruction
import ARS_Coverage
import ARS_CoverageClass
import ARS_CylinderDomination
import ARS_CylinderLaw
import ARS_CylinderRecovery
import ARS_GameLoss
import ARS_GameLossJoint
import ARS_NativeAccount
import ARS_NativeCost
import ARS_NativeOutcome
import ARS_Nonvacuity
import ARS_PaddedSupport
import ARS_QueryCost
import ARS_QueryTransport
import ARS_ReachedBudget
import ARS_ReachedCharge
import ARS_ReachedMass
import ARS_ReachedNumeric
import ARS_ReachedZero
import ARS_SupportedCarrier
import ARS_WorldCylinder
import Rc10_Top
set_option autoImplicit false

#print axioms AspisR1.ARS_AccountDomination.pointwise
#print axioms AspisR1.ARS_AccountReplay.replay
#print axioms AspisR1.ARS_AccountReplay.supported
#print axioms AspisR1.ARS_AccountReplay.law
#print axioms AspisR1.ARS_AccountReplay.runtime
#print axioms AspisR1.ARS_AccountReplay.first
#print axioms AspisR1.ARS_AdaptiveCost.second
#print axioms AspisR1.ARS_AdaptiveCost.outcome
#print axioms AspisR1.ARS_AdaptiveCost.count
#print axioms AspisR1.ARS_AdaptiveCost.unbounded
#print axioms AspisR1.ARS_BudgetFromTotal.choice
#print axioms AspisR1.ARS_BudgetFromTotal.first
#print axioms AspisR1.ARS_Carrier.projection
#print axioms AspisR1.ARS_Carrier.checkpoint
#print axioms AspisR1.ARS_Chronology.component
#print axioms AspisR1.ARS_Chronology.pieces
#print axioms AspisR1.ARS_ConditionalMass.bound
#print axioms AspisR1.ARS_ConditionalNumeric.numeric
#print axioms AspisR1.ARS_CostObstruction.no_total_budget
#print axioms AspisR1.ARS_Coverage.deployed
#print axioms AspisR1.ARS_CoverageClass.iff_issued
#print axioms AspisR1.ARS_CylinderDomination.pointwise
#print axioms AspisR1.ARS_CylinderLaw.mean
#print axioms AspisR1.ARS_CylinderRecovery.extract
#print axioms AspisR1.ARS_GameLoss.rejects
#print axioms AspisR1.ARS_GameLoss.allowed
#print axioms AspisR1.ARS_GameLossJoint.permitted
#print axioms AspisR1.ARS_NativeAccount.exact
#print axioms AspisR1.ARS_NativeCost.read_count
#print axioms AspisR1.ARS_NativeCost.exact
#print axioms AspisR1.ARS_NativeOutcome.source
#print axioms AspisR1.ARS_Nonvacuity.conditional
#print axioms AspisR1.ARS_PaddedSupport.unbounded
#print axioms AspisR1.ARS_QueryCost.count
#print axioms AspisR1.ARS_QueryCost.law
#print axioms AspisR1.ARS_QueryTransport.covered
#print axioms AspisR1.ARS_QueryTransport.exact
#print axioms AspisR1.ARS_QueryTransport.accepted
#print axioms AspisR1.ARS_ReachedBudget.issued
#print axioms AspisR1.ARS_ReachedCharge.charged
#print axioms AspisR1.ARS_ReachedMass.bound
#print axioms AspisR1.ARS_ReachedNumeric.numeric
#print axioms AspisR1.ARS_ReachedZero.zero
#print axioms AspisR1.ARS_SupportedCarrier.deployed
#print axioms AspisR1.ARS_WorldCylinder.reads_consistent
#print axioms AspisR1.ARS_WorldCylinder.agrees_of_same
#print axioms AspisR1.ARS_WorldCylinder.iff_same
#print axioms AspisR1.ARS_WorldCylinder.different_execution
#print axioms AspisR1.Rc10_Top.deployed

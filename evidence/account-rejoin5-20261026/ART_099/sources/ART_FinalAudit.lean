import ART_AcceptedBridge
import ART_AccountAccepted
import ART_AccountChronology
import ART_AdversaryWork
import ART_Carrier
import ART_ChargeEquality
import ART_ConditionalNumeric
import ART_Cost
import ART_Coverage
import ART_CylinderDomination
import ART_CylinderRecovery
import ART_FirstProjection
import ART_FullBudget
import ART_FullCharge
import ART_NativeAccepted
import ART_NativeAgreement
import ART_NativeCertificate
import ART_NativeCoverage
import ART_NoFactory
import ART_Nonvacuity
import ART_OriginalLaw
import ART_Outcome
import ART_OutcomeMixture
import ART_PartialAccount
import ART_PartialExact
import ART_PartialProgram
import ART_PhysicalView
import ART_PrefixCoupling
import ART_QueriedCoverage
import ART_QueriedLaw
import ART_QueriedPieces
import ART_QueriedRuntime
import ART_QueryAgreement
import ART_QueryCylinder
import ART_QueryRestricted
import ART_RejectedDigest
import ART_RejectedFirst
import ART_RejectedNative
import ART_RootObstruction
import ART_Runtime
import ART_RuntimeAccepted
import ART_RuntimeDomination
import ART_StartCharge
import ART_StartFromWork
import ART_StartMass
import ART_StartPrefix
import ART_SupportObstruction
import ART_SyscallObstruction
import ART_WrapperAccepted
import ART_WrapperBudget
import ART_WrapperExact
import ART_ZeroArithmetic
import Rc10_Top
import SCJ_Composition
set_option autoImplicit false
#print axioms AspisR1.ART_AcceptedBridge.source
#print axioms AspisR1.ART_AccountAccepted.exact
#print axioms AspisR1.ART_AccountChronology.first_ok
#print axioms AspisR1.ART_AccountChronology.first_reject
#print axioms AspisR1.ART_AdversaryWork.first
#print axioms AspisR1.ART_AdversaryWork.phases
#print axioms AspisR1.ART_Carrier.projection
#print axioms AspisR1.ART_Carrier.checkpoint
#print axioms AspisR1.ART_ChargeEquality.accepted
#print axioms AspisR1.ART_ConditionalNumeric.numeric
#print axioms AspisR1.ART_Cost.represented
#print axioms AspisR1.ART_Cost.exact
#print axioms AspisR1.ART_Coverage.execution
#print axioms AspisR1.ART_CylinderDomination.pointwise
#print axioms AspisR1.ART_CylinderRecovery.extract
#print axioms AspisR1.ART_FirstProjection.original
#print axioms AspisR1.ART_FullBudget.issued
#print axioms AspisR1.ART_FullCharge.charged
#print axioms AspisR1.ART_NativeAccepted.accepted
#print axioms AspisR1.ART_NativeAgreement.issued
#print axioms AspisR1.ART_NativeCertificate.original
#print axioms AspisR1.ART_NativeCoverage.original
#print axioms AspisR1.ART_NoFactory.impossible
#print axioms AspisR1.ART_Nonvacuity.conditional
#print axioms AspisR1.ART_OriginalLaw.exact
#print axioms AspisR1.ART_Outcome.represented
#print axioms AspisR1.ART_Outcome.exact
#print axioms AspisR1.ART_Outcome.native
#print axioms AspisR1.ART_OutcomeMixture.law
#print axioms AspisR1.ART_PartialExact.execution
#print axioms AspisR1.ART_PartialExact.cost
#print axioms AspisR1.ART_PartialExact.addresses
#print axioms AspisR1.ART_PartialExact.law
#print axioms AspisR1.ART_PartialProgram.exact
#print axioms AspisR1.ART_PhysicalView.accepted
#print axioms AspisR1.ART_PhysicalView.replay
#print axioms AspisR1.ART_PrefixCoupling.source
#print axioms AspisR1.ART_PrefixCoupling.cost
#print axioms AspisR1.ART_QueriedCoverage.original
#print axioms AspisR1.ART_QueriedLaw.original
#print axioms AspisR1.ART_QueriedPieces.chronology
#print axioms AspisR1.ART_QueriedRuntime.exact
#print axioms AspisR1.ART_QueryAgreement.compatible
#print axioms AspisR1.ART_QueryCylinder.outside
#print axioms AspisR1.ART_QueryCylinder.no_global
#print axioms AspisR1.ART_QueryCylinder.strict
#print axioms AspisR1.ART_QueryRestricted.installed
#print axioms AspisR1.ART_RejectedDigest.failed
#print axioms AspisR1.ART_RejectedDigest.diverged
#print axioms AspisR1.ART_RejectedDigest.stopped
#print axioms AspisR1.ART_RejectedFirst.no_second
#print axioms AspisR1.ART_RejectedNative.mass
#print axioms AspisR1.ART_RootObstruction.independent
#print axioms AspisR1.ART_Runtime.eval_runtime
#print axioms AspisR1.ART_Runtime.rejected
#print axioms AspisR1.ART_RuntimeAccepted.exact
#print axioms AspisR1.ART_RuntimeDomination.pointwise
#print axioms AspisR1.ART_RuntimeDomination.averaged
#print axioms AspisR1.ART_StartCharge.first_starts
#print axioms AspisR1.ART_StartCharge.total_starts
#print axioms AspisR1.ART_StartFromWork.starts
#print axioms AspisR1.ART_StartMass.bound
#print axioms AspisR1.ART_StartPrefix.original_index
#print axioms AspisR1.ART_StartPrefix.predecessor_index
#print axioms AspisR1.ART_SupportObstruction.no_entry
#print axioms AspisR1.ART_SyscallObstruction.no_native_world
#print axioms AspisR1.ART_WrapperAccepted.exact
#print axioms AspisR1.ART_WrapperBudget.first
#print axioms AspisR1.ART_WrapperBudget.second
#print axioms AspisR1.ART_WrapperExact.execution
#print axioms AspisR1.ART_ZeroArithmetic.margin
#print axioms AspisR1.ART_ZeroArithmetic.positive
#print axioms AspisR1.ART_ZeroArithmetic.doubled_shortfall
#print axioms AspisR1.ART_ZeroArithmetic.first_fraction
#print axioms AspisR1.Rc10_Top.deployed
#check @AspisR1.SCJ_Composition.account_of_branch
#print axioms AspisR1.SCJ_Composition.account_of_branch

import ARU_AllWorld
import ARU_AuditAccountCuts
import ARU_AuditAllWorldMean
import ARU_AuditCarrier
import ARU_AuditCheckpointBank
import ARU_AuditCollisionCharge
import ARU_AuditCoverageQuantifiers
import ARU_AuditDomination
import ARU_AuditFinishOwners
import ARU_AuditFrozenConstants
import ARU_AuditFullWork
import ARU_AuditInstalledSource
import ARU_AuditLocalOracle
import ARU_AuditNonvacuity
import ARU_AuditOriginalFactory
import ARU_AuditOriginalLaw
import ARU_AuditRecovery
import ARU_AuditRejectedPrefixes
import ARU_AuditRootScope
import ARU_AuditRuntimeRestriction
import ARU_BankTransport
import ARU_BeforeRoot
import ARU_ByteMatch
import ARU_Carrier
import ARU_Charge
import ARU_Charges
import ARU_Checkpoint
import ARU_Coverage
import ARU_CoverageQuantifiers
import ARU_Cuts
import ARU_CutsOrigin
import ARU_DecodedOrigin
import ARU_Domination
import ARU_EventInclusion
import ARU_EventMass
import ARU_Factory
import ARU_FiniteIssued
import ARU_FirstHeader
import ARU_FirstPair
import ARU_FullBoundary
import ARU_FullSourceAlternative
import ARU_Header
import ARU_IndexedFactory
import ARU_IndexedOriginalLaw
import ARU_Issued
import ARU_IssuedMismatch
import ARU_Join
import ARU_Mass
import ARU_NativeReplies
import ARU_Nonvacuity
import ARU_Numeric
import ARU_ObstructionResolved
import ARU_OracleLog
import ARU_OriginalAverage
import ARU_OriginalDomination
import ARU_OriginalFactory
import ARU_OriginalLaw
import ARU_OriginalRecovery
import ARU_OriginalSupport
import ARU_PartialAccepted
import ARU_PartialFactory
import ARU_PerCoin
import ARU_R1
import ARU_Range
import ARU_ReadHead
import ARU_ReaderHeader
import ARU_ReaderReached
import ARU_RecoveryBranch
import ARU_Replies
import ARU_Returning
import ARU_RootRestriction
import ARU_RuntimeMass
import ARU_SecondHeader
import ARU_SecondPair
import ARU_Selector
import ARU_SelectorPure
import ARU_SourceAlternative
import ARU_SourceResults
import ARU_Support
import ARU_Whole
import ARU_WrapperAccepted
import ARU_WrapperSource
import ARU_WriterHeader
import ARU_WriterReached
set_option autoImplicit false
#print axioms AspisR1.ARU_AllWorld.clean
#print axioms AspisR1.ARU_BankTransport.deployed
#print axioms AspisR1.ARU_ByteMatch.digest_matches
#print axioms AspisR1.ARU_Carrier.exact
#print axioms AspisR1.ARU_Charge.cached_preparation
#print axioms AspisR1.ARU_Charges.charged
#print axioms AspisR1.ARU_Checkpoint.selected
#print axioms AspisR1.ARU_Coverage.original
#print axioms AspisR1.ARU_CoverageQuantifiers.exact_iff
#print axioms AspisR1.ARU_Cuts.selected
#print axioms AspisR1.ARU_CutsOrigin.selected
#print axioms AspisR1.ARU_DecodedOrigin.pair
#print axioms AspisR1.ARU_Domination.pointwise
#print axioms AspisR1.ARU_EventInclusion.inclusion
#print axioms AspisR1.ARU_EventMass.mass
#print axioms AspisR1.ARU_Factory.deployed
#print axioms AspisR1.ARU_FiniteIssued.finite
#print axioms AspisR1.ARU_FiniteIssued.transport
#print axioms AspisR1.ARU_FirstHeader.accepted
#print axioms AspisR1.ARU_FirstPair.same_pair
#print axioms AspisR1.ARU_FullBoundary.same_cuts
#print axioms AspisR1.ARU_FullSourceAlternative.accepted
#print axioms AspisR1.ARU_Header.reader
#print axioms AspisR1.ARU_Header.writer
#print axioms AspisR1.ARU_IndexedFactory.original_law
#print axioms AspisR1.ARU_IndexedOriginalLaw.original_law
#print axioms AspisR1.ARU_Issued.derive
#print axioms AspisR1.ARU_IssuedMismatch.different_execution
#print axioms AspisR1.ARU_IssuedMismatch.excluded
#print axioms AspisR1.ARU_Join.accepted
#print axioms AspisR1.ARU_Mass.conditional
#print axioms AspisR1.ARU_NativeReplies.accepted
#print axioms AspisR1.ARU_Nonvacuity.conditional
#print axioms AspisR1.ARU_Numeric.conditional
#print axioms AspisR1.ARU_ObstructionResolved.installed
#print axioms AspisR1.ARU_OracleLog.agrees
#print axioms AspisR1.ARU_OracleLog.coherent
#print axioms AspisR1.ARU_OriginalAverage.averaged
#print axioms AspisR1.ARU_OriginalDomination.pointwise
#print axioms AspisR1.ARU_OriginalFactory.original
#print axioms AspisR1.ARU_OriginalLaw.exact
#print axioms AspisR1.ARU_OriginalRecovery.extract
#print axioms AspisR1.ARU_OriginalSupport.original
#print axioms AspisR1.ARU_PartialAccepted.accepted
#print axioms AspisR1.ARU_PartialFactory.original
#print axioms AspisR1.ARU_PerCoin.extract
#print axioms AspisR1.ARU_R1.selected
#print axioms AspisR1.ARU_Range.conditional
#print axioms AspisR1.ARU_ReadHead.issued
#print axioms AspisR1.ARU_ReaderHeader.ideal
#print axioms AspisR1.ARU_ReaderReached.reached
#print axioms AspisR1.ARU_RecoveryBranch.accepted
#print axioms AspisR1.ARU_Replies.accepted
#print axioms AspisR1.ARU_Returning.returning
#print axioms AspisR1.ARU_Returning.safe
#print axioms AspisR1.ARU_RootRestriction.impossible_if_native
#print axioms AspisR1.ARU_RuntimeMass.pointwise
#print axioms AspisR1.ARU_SecondHeader.accepted
#print axioms AspisR1.ARU_SecondPair.same_pair
#print axioms AspisR1.ARU_Selector.selected
#print axioms AspisR1.ARU_SelectorPure.account
#print axioms AspisR1.ARU_SelectorPure.pair
#print axioms AspisR1.ARU_SelectorPure.public2
#print axioms AspisR1.ARU_SourceAlternative.accepted
#print axioms AspisR1.ARU_SourceResults.accepted
#print axioms AspisR1.ARU_Whole.same_cuts
#print axioms AspisR1.ARU_WrapperAccepted.first
#print axioms AspisR1.ARU_WrapperAccepted.second
#print axioms AspisR1.ARU_WrapperSource.first
#print axioms AspisR1.ARU_WrapperSource.second
#print axioms AspisR1.ARU_WriterHeader.ideal
#print axioms AspisR1.ARU_WriterReached.reached
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.ART_RootObstruction.independent
#print axioms AspisR1.SCJ_NativeLoaded.ideal_cut
#print axioms AspisR1.SCI_Recovery.account_extract

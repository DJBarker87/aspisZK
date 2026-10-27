import FJo_ClosureAudit
import FJp_ARCore
import FJp_AccountJoin
import FJp_ActualCaller
import FJp_ActualCont
import FJp_ActualLiteral
import FJp_Bound
import FJp_CallerForget
import FJp_CircleTransport
import FJp_CollisionLaw
import FJp_ConsSecond
import FJp_Conservativity
import FJp_ContForget
import FJp_Cost
import FJp_Domination
import FJp_Fin22
import FJp_FinalObservations
import FJp_Finish
import FJp_GlobalOwners
import FJp_GlobalScopeAudit
import FJp_GlobalTop
import FJp_Join
import FJp_KernelComparison
import FJp_LiteralForget
import FJp_LiteralJoin
import FJp_Mass
import FJp_MatchingAt
import FJp_MatchingJoin
import FJp_MatchingLaw
import FJp_Native
import FJp_NativeBuilder
import FJp_NativeFirst
import FJp_NativeJoin
import FJp_NativeLiteral
import FJp_NativePair
import FJp_NativeReader
import FJp_NativeScopeAudit
import FJp_Nonvacuity
import FJp_Observations
import FJp_ObservedMatch
import FJp_PhaseObservation
import FJp_PhaseReady
import FJp_Query00
import FJp_Query01
import FJp_Query02
import FJp_Query03
import FJp_Query04
import FJp_Query05
import FJp_Query06
import FJp_Query07
import FJp_Query08
import FJp_Query09
import FJp_Query10
import FJp_Query11
import FJp_Query12
import FJp_Query13
import FJp_Query14
import FJp_Query15
import FJp_Query16
import FJp_Query17
import FJp_Query18
import FJp_Query19
import FJp_Query20
import FJp_Query21
import FJp_QueryLaw
import FJp_QueryValues
import FJp_RecoveryBranch
import FJp_Remaining
import FJp_Residual
import FJp_Result
import FJp_ResultForget
import FJp_RetDefinitions
import FJp_RetPrefix
import FJp_RetRc7
import FJp_RetSuffix
import FJp_RootBinding
import FJp_SourceValues
import FJp_Statements
import FJp_Top

#print axioms AspisR1.FJp_ARCore.observations
#print axioms AspisR1.FJp_AccountJoin.accepted
#print axioms AspisR1.FJp_ActualCaller.strengthen
#print axioms AspisR1.FJp_ActualCont.strengthen
#print axioms AspisR1.FJp_ActualLiteral.strengthen
#print axioms AspisR1.FJp_Bound.bound
#print axioms AspisR1.FJp_CallerForget.value
#print axioms AspisR1.FJp_CircleTransport.alpha
#print axioms AspisR1.FJp_CircleTransport.x
#print axioms AspisR1.FJp_CircleTransport.y
#print axioms AspisR1.FJp_CircleTransport.dots
#print axioms AspisR1.FJp_CollisionLaw.joined
#print axioms AspisR1.FJp_ConsSecond.accepted
#print axioms AspisR1.FJp_Conservativity.deployed
#print axioms AspisR1.FJp_ContForget.value
#print axioms AspisR1.FJp_Cost.source_cost
#print axioms AspisR1.FJp_Domination.pointwise
#print axioms AspisR1.FJp_Fin22.all
#print axioms AspisR1.FJp_FinalObservations.observations
#print axioms AspisR1.FJp_Finish.strengthen
#print axioms AspisR1.FJp_Finish.forget
#print axioms AspisR1.FJp_GlobalOwners.of_original
#print axioms AspisR1.FJp_GlobalOwners.weaken
#print axioms AspisR1.FJp_GlobalTop.deployed
#print axioms AspisR1.FJp_Join.accepted_raw_join_or_collision
#print axioms AspisR1.FJp_LiteralForget.value
#print axioms AspisR1.FJp_LiteralJoin.value
#print axioms AspisR1.FJp_Mass.bounded
#print axioms AspisR1.FJp_MatchingAt.value
#print axioms AspisR1.FJp_MatchingJoin.value
#print axioms AspisR1.FJp_MatchingLaw.value
#print axioms AspisR1.FJp_NativeBuilder.accepted
#print axioms AspisR1.FJp_NativeFirst.value
#print axioms AspisR1.FJp_NativeJoin.value
#print axioms AspisR1.FJp_NativeLiteral.strengthen
#print axioms AspisR1.FJp_NativePair.value
#print axioms AspisR1.FJp_NativeReader.alpha
#print axioms AspisR1.FJp_Nonvacuity.owners
#print axioms AspisR1.FJp_Observations.observations
#print axioms AspisR1.FJp_ObservedMatch.value
#print axioms AspisR1.FJp_Query00.value
#print axioms AspisR1.FJp_Query01.value
#print axioms AspisR1.FJp_Query02.value
#print axioms AspisR1.FJp_Query03.value
#print axioms AspisR1.FJp_Query04.value
#print axioms AspisR1.FJp_Query05.value
#print axioms AspisR1.FJp_Query06.value
#print axioms AspisR1.FJp_Query07.value
#print axioms AspisR1.FJp_Query08.value
#print axioms AspisR1.FJp_Query09.value
#print axioms AspisR1.FJp_Query10.value
#print axioms AspisR1.FJp_Query11.value
#print axioms AspisR1.FJp_Query12.value
#print axioms AspisR1.FJp_Query13.value
#print axioms AspisR1.FJp_Query14.value
#print axioms AspisR1.FJp_Query15.value
#print axioms AspisR1.FJp_Query16.value
#print axioms AspisR1.FJp_Query17.value
#print axioms AspisR1.FJp_Query18.value
#print axioms AspisR1.FJp_Query19.value
#print axioms AspisR1.FJp_Query20.value
#print axioms AspisR1.FJp_Query21.value
#print axioms AspisR1.FJp_QueryValues.value
#print axioms AspisR1.FJp_RecoveryBranch.accepted
#print axioms AspisR1.FJp_Remaining.complete
#print axioms AspisR1.FJp_Residual.numeric
#print axioms AspisR1.FJp_Residual.margin_exact
#print axioms AspisR1.FJp_Result.strengthen
#print axioms AspisR1.FJp_ResultForget.value
#print axioms AspisR1.FJp_Ret_PairSelected.accepted
#print axioms AspisR1.FJp_Ret_ActualPair.accepted
#print axioms AspisR1.FJp_Ret_ClosedPair.accepted
#print axioms AspisR1.FJp_Ret_DirectPair.accepted
#print axioms AspisR1.FJp_Ret_LiteralPair.accepted
#print axioms AspisR1.FJp_Ret_LiteralTop.deployed
#print axioms AspisR1.FJp_Ret_R3Top.deployed
#print axioms AspisR1.FJp_Ret_Rc7Native.accepted
#print axioms AspisR1.FJp_Ret_SafResult.strengthen
#print axioms AspisR1.FJp_Ret_SafTop.deployed
#print axioms AspisR1.FJp_Ret_FinalResult.strengthen
#print axioms AspisR1.FJp_Ret_FinalTop.deployed
#print axioms AspisR1.FJp_Ret_Deployed.deployed
#print axioms AspisR1.FJp_Ret_Source.source
#print axioms AspisR1.FJp_Ret_R5Close.from_saf
#print axioms AspisR1.FJp_Ret_R6Result.strengthen
#print axioms AspisR1.FJp_Ret_Release.remove
#print axioms AspisR1.FJp_SourceValues.value
#print axioms AspisR1.FJp_Top.deployed
#print axioms AspisR1.ARX_Root.deployed

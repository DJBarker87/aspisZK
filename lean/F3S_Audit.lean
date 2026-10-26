import F3S_AcceptanceValues
import F3S_BatchDictionary
import F3S_BatchLoop
import F3S_BatchTree
import F3S_CheckpointNative
import F3S_CheckpointOnRun
import F3S_CheckpointSplice
import F3S_ChildLogs
import F3S_Chronology
import F3S_Complete
import F3S_ConsPrepared
import F3S_Containing
import F3S_Dictionary
import F3S_EffectDictionary
import F3S_EffectLog
import F3S_ExactChildren
import F3S_FinishContinuation
import F3S_FinishReached
import F3S_FinishUnique
import F3S_FinishWitness
import F3S_FirstBase
import F3S_FirstHeader
import F3S_FirstOnRun
import F3S_FirstPairLog
import F3S_FirstRecords
import F3S_FirstRun
import F3S_FirstSplice
import F3S_FirstTail
import F3S_FirstTailCode
import F3S_FirstTailLogs
import F3S_Forward
import F3S_InputAtSecond
import F3S_Join
import F3S_Located
import F3S_MapLog
import F3S_ModelAcceptance
import F3S_ModelLog
import F3S_NativeChildren
import F3S_NativePrepareLog
import F3S_PairBatches
import F3S_PairCheckpointLog
import F3S_PairFinish
import F3S_PairModelFinish
import F3S_PrimitiveNonvacuity
import F3S_ReaderSkeleton
import F3S_ReaderSyntax
import F3S_Residual
import F3S_RoundUnique
import F3S_RoundValues
import F3S_RunCalls
import F3S_SdkDictionary
import F3S_SecondCommon
import F3S_SecondOnRun
import F3S_SecondProvenance
import F3S_SecondRecords
import F3S_SecondRoot
import F3S_SecondSplice
import F3S_Segments
import F3S_Silent
import F3S_TwoRecords
import F3S_TwoSegments

/- Focused final audit; no package or frozen-release replay. -/
#print axioms AspisR1.F3S_BatchDictionary.values
#print axioms AspisR1.F3S_BatchDictionary.code
#print axioms AspisR1.F3S_BatchDictionary.current
#print axioms AspisR1.F3S_BatchDictionary.stage
#print axioms AspisR1.F3S_BatchLoop.dictionary
#print axioms AspisR1.F3S_BatchTree.dictionary
#print axioms AspisR1.F3S_CheckpointNative.accepted
#print axioms AspisR1.F3S_CheckpointOnRun.log
#print axioms AspisR1.F3S_CheckpointSplice.raw
#print axioms AspisR1.F3S_CheckpointSplice.writer
#print axioms AspisR1.F3S_ChildLogs.first
#print axioms AspisR1.F3S_Chronology.log
#print axioms AspisR1.F3S_Complete.accepted_values
#print axioms AspisR1.F3S_ConsPrepared.from_cut
#print axioms AspisR1.F3S_Containing.split
#print axioms AspisR1.F3S_Dictionary.first
#print axioms AspisR1.F3S_Dictionary.second
#print axioms AspisR1.F3S_EffectDictionary.run
#print axioms AspisR1.F3S_EffectLog.accepted
#print axioms AspisR1.F3S_ExactChildren.exact_children
#print axioms AspisR1.F3S_FinishContinuation.reached
#print axioms AspisR1.F3S_FinishReached.reached
#print axioms AspisR1.F3S_FinishUnique.unique
#print axioms AspisR1.F3S_FinishWitness.source
#print axioms AspisR1.F3S_FirstBase.preparation
#print axioms AspisR1.F3S_FirstHeader.split
#print axioms AspisR1.F3S_FirstOnRun.log
#print axioms AspisR1.F3S_FirstPairLog.log
#print axioms AspisR1.F3S_FirstRecords.first_records
#print axioms AspisR1.F3S_FirstRun.first_run
#print axioms AspisR1.F3S_FirstSplice.split
#print axioms AspisR1.F3S_FirstTail.split
#print axioms AspisR1.F3S_FirstTailLogs.on_calls
#print axioms AspisR1.F3S_Forward.lift_ok
#print axioms AspisR1.F3S_Forward.bind_log
#print axioms AspisR1.F3S_InputAtSecond.facts
#print axioms AspisR1.F3S_Join.accepted_log_eq
#print axioms AspisR1.F3S_Located.singleton
#print axioms AspisR1.F3S_Located.on_log
#print axioms AspisR1.F3S_MapLog.run_map
#print axioms AspisR1.F3S_ModelAcceptance.accepted
#print axioms AspisR1.F3S_ModelLog.schedule
#print axioms AspisR1.F3S_NativeChildren.on_pair
#print axioms AspisR1.F3S_NativePrepareLog.accepted
#print axioms AspisR1.F3S_PairBatches.accepted
#print axioms AspisR1.F3S_PairCheckpointLog.accepted
#print axioms AspisR1.F3S_PairFinish.accepted
#print axioms AspisR1.F3S_PairModelFinish.accepted
#print axioms AspisR1.F3S_PrimitiveNonvacuity.accepted
#print axioms AspisR1.F3S_ReaderSkeleton.native
#print axioms AspisR1.F3S_ReaderSkeleton.retained
#print axioms AspisR1.F3S_ReaderSyntax.program
#print axioms AspisR1.F3S_ReaderSyntax.log
#print axioms AspisR1.F3S_Residual.impossible
#print axioms AspisR1.F3S_RoundUnique.record
#print axioms AspisR1.F3S_RoundUnique.values
#print axioms AspisR1.F3S_RoundValues.reached
#print axioms AspisR1.F3S_RunCalls.source
#print axioms AspisR1.F3S_SdkDictionary.sdk
#print axioms AspisR1.F3S_SecondCommon.split
#print axioms AspisR1.F3S_SecondOnRun.log
#print axioms AspisR1.F3S_SecondProvenance.split
#print axioms AspisR1.F3S_SecondRecords.second_records
#print axioms AspisR1.F3S_SecondRoot.split
#print axioms AspisR1.F3S_SecondSplice.split
#print axioms AspisR1.F3S_Segments.projection
#print axioms AspisR1.F3S_Segments.chronological
#print axioms AspisR1.F3S_Silent.lift_log
#print axioms AspisR1.F3S_TwoRecords.accepted
#print axioms AspisR1.F3S_TwoSegments.shape

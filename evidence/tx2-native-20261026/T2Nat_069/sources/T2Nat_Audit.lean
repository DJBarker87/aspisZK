import T2Nat_NativePair
import T2Nat_FinishNonvacuity
import T2Nat_ReaderNonvacuity

#print axioms AspisR1.T2Nat_Accepted.accepted_pair_unified
#print axioms AspisR1.T2Nat_AfterQueries.normalize
#print axioms AspisR1.T2Nat_CodeEq.refl
#print axioms AspisR1.T2Nat_CodeEq.lift
#print axioms AspisR1.T2Nat_CodeEq.bind
#print axioms AspisR1.T2Nat_CodeIf.branches
#print axioms AspisR1.T2Nat_FinishCode.parent_erase
#print axioms AspisR1.T2Nat_FinishCode.parent_effects
#print axioms AspisR1.T2Nat_FinishNonvacuity.success_log
#print axioms AspisR1.T2Nat_FinishNonvacuity.round_fission
#print axioms AspisR1.T2Nat_FinishResult.installed_erase
#print axioms AspisR1.T2Nat_FinishResult.installed_effects
#print axioms AspisR1.T2Nat_FinishResult.accepted_effects
#print axioms AspisR1.T2Nat_FinishResult.full_result
#print axioms AspisR1.T2Nat_NativePair.accepted_pair_unified
#print axioms AspisR1.T2Nat_QueryJoin.afterQueries
#print axioms AspisR1.T2Nat_QueryJoin.queries
#print axioms AspisR1.T2Nat_QueryReads.congr
#print axioms AspisR1.T2Nat_QuerySource.normalize
#print axioms AspisR1.T2Nat_RawBounds.range_success
#print axioms AspisR1.T2Nat_RawBounds.checked_success
#print axioms AspisR1.T2Nat_RawBounds.no_wrap
#print axioms AspisR1.T2Nat_RawBounds.current_success
#print axioms AspisR1.T2Nat_RawJoin.checked_add
#print axioms AspisR1.T2Nat_RawJoin.normalization
#print axioms AspisR1.T2Nat_RawJoin.reference
#print axioms AspisR1.T2Nat_RawJoin.success_iff
#print axioms AspisR1.T2Nat_RawStage.congr
#print axioms AspisR1.T2Nat_ReadCongr.withK
#print axioms AspisR1.T2Nat_ReaderBody.source
#print axioms AspisR1.T2Nat_ReaderEffects.header
#print axioms AspisR1.T2Nat_ReaderEffects.program
#print axioms AspisR1.T2Nat_ReaderEffects.source
#print axioms AspisR1.T2Nat_ReaderEffects.on_run
#print axioms AspisR1.T2Nat_ReaderFission.source
#print axioms AspisR1.T2Nat_ReaderJoin.header
#print axioms AspisR1.T2Nat_ReaderJoin.resume
#print axioms AspisR1.T2Nat_ReaderJoin.reader_eq
#print axioms AspisR1.T2Nat_ReaderJoin.on_run
#print axioms AspisR1.T2Nat_ReaderNonvacuity.size_s2
#print axioms AspisR1.T2Nat_ReaderNonvacuity.empty_rejects
#print axioms AspisR1.T2Nat_ReaderNonvacuity.raw_total
#print axioms AspisR1.T2Nat_ReaderOps.unwrap_ok
#print axioms AspisR1.T2Nat_ReaderOps.raw
#print axioms AspisR1.T2Nat_ReaderOps.readK
#print axioms AspisR1.T2Nat_ReaderOps.readE
#print axioms AspisR1.T2Nat_ReaderOps.semantic
#print axioms AspisR1.T2Nat_ReaderOps.weights
#print axioms AspisR1.T2Nat_ReaderOps.validate
#print axioms AspisR1.T2Nat_ReaderPrefix.source_eq
#print axioms AspisR1.T2Nat_ReaderPrefix.normalize
#print axioms AspisR1.T2Nat_ReaderSuffix.normalize
#print axioms AspisR1.T2Nat_ResultEq.refl
#print axioms AspisR1.T2Nat_ResultEq.symm
#print axioms AspisR1.T2Nat_ResultEq.bind_success
#print axioms AspisR1.T2Nat_ResultEq.bind
#print axioms AspisR1.T2Nat_ResumeCode.source
#print axioms AspisR1.T2Nat_ResumeCode.congr
#print axioms AspisR1.T2Nat_ResumePrefix.source
#print axioms AspisR1.T2Nat_ResumePrefix.congr
#print axioms AspisR1.T2Nat_RoundCode.round_erase
#print axioms AspisR1.T2Nat_RoundCode.round_effects
#print axioms AspisR1.T2Nat_ScalarJoin.raw_eq
#print axioms AspisR1.T2Nat_ScalarJoin.k_eq
#print axioms AspisR1.T2Nat_ScalarJoin.e_eq
#print axioms AspisR1.T2Nat_ScalarStage.congr
#print axioms AspisR1.T2Nat_SemanticJoin.congr
#print axioms AspisR1.T2Nat_SemanticJoin.reference
#print axioms AspisR1.T2Nat_Silent.erase_bind
#print axioms AspisR1.T2Nat_Silent.erase_call
#print axioms AspisR1.T2Nat_Silent.erase_pure
#print axioms AspisR1.T2Nat_Silent.code_erase
#print axioms AspisR1.T2Nat_Silent.ordered_log
#print axioms AspisR1.T2Nat_SuffixJoin.normalized
#print axioms AspisR1.T2Nat_TailFactor.source_eq
#print axioms AspisR1.T2Nat_TailFactor.congr
#print axioms AspisR1.T2Nat_TailJoin.normalized
#print axioms AspisR1.T2Nat_TailJoin.source
#print axioms AspisR1.T2Nat_Try.branch
#print axioms AspisR1.T2Nat_Try.read_congr
#print axioms AspisR1.T2Nat_Try.ok_congr
#print axioms AspisR1.T2Nat_WeightLoop.normalize
#print axioms AspisR1.T2Nat_WeightSequence.sequence
#print axioms AspisR1.T2Nat_WeightSequence.weights
#print axioms AspisR1.T2Nat_WeightSequence.native
#print axioms AspisR1.T2Nat_WeightsCongr.reads
#print axioms AspisR1.T2Nat_WeightsCongr.weights
#print axioms AspisR1.T2Nat_WeightsCongr.native

#print AspisR1.T2Nat_ResultEq.EqOk
#print AspisR1.T2Nat_CodeEq.EqRun
#print AspisR1.T2Nat_ReaderOps.ops
#print AspisR1.T2Nat_ReaderJoin.reader
#print AspisR1.T2Nat_ReaderEffects.OnRun
#print AspisR1.T2Nat_FinishResult.installed

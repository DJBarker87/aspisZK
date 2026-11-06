import NJO_COMBINED_IMPORT
import NJR_COMBINED_IMPORT
import NJU_BadWindow
import NJU_CommonObserved
import NJU_CurrentWindows
import NJU_FieldDecode
import NJU_FieldFailure
import NJU_FieldScalar
import NJU_FinishAtCurrent
import NJU_FinishCaller
import NJU_FinishCase
import NJU_FinishCore
import NJU_FinishDomain
import NJU_FinishInput
import NJU_FinishInstall
import NJU_FinishObserved
import NJU_GeneralFinishRoot
import NJU_Log
import NJU_ResumeErase
import NJU_ResumeObserved
import NJU_ResumeReference
import NJU_ResumeRoot
import NJU_RootAudit
import NJU_ViewWindows
import NJU_WeakAlignAfterPhase
import NJU_WeakAlignAllocatorPhase
import NJU_WeakAlignPairPhase
import NJU_WeakAlignPairPhaseSource
import NJU_WeakAlignRegularPhase
import NJU_WeakAlignRegularPhaseSource
import NJU_WeakAlignSharedPhase
import NJU_WeakAllocatorChain
import NJU_WeakAllocatorInstantiation
import NJU_WeakFinishComposedLog
import NJU_WeakFinishObserved
import NJU_WeakFinishPairCertificate
import NJU_WeakFinishPort
import NJU_WeakPairCaller
import NJU_WeakPairDomain
import NJU_WeakPairInstalled
import NJU_WeakPairInstantiation
import NJU_WeakRegularChain
import NJU_WeakRegularContinuation
import NJU_WeakSharedChain
import NJU_WeakSharedComplete
#print axioms NJU_BadWindow.witness
#print axioms NJU_BadWindow.noncanonical
#print axioms NJU_BadWindow.read_bounds
#print axioms NJU_BadWindow.short
#print axioms NJU_CommonObserved.source
#print axioms NJU_CurrentWindows.split
#print axioms NJU_CurrentWindows.rejects
#print axioms NJU_FieldDecode.total
#print axioms NJU_FieldDecode.word_value
#print axioms NJU_FieldDecode.none_of_bad
#print axioms NJU_FieldDecode.slice_none
#print axioms NJU_FieldFailure.noncanonical
#print axioms NJU_FieldFailure.short
#print axioms NJU_FieldFailure.primitive_noncanonical
#print axioms NJU_FieldScalar.eq_of_value
#print axioms NJU_FieldScalar.checked
#print axioms NJU_FieldScalar.abort_none
#print axioms NJU_FieldScalar.abort_short
#print axioms NJU_FieldScalar.returns
#print axioms NJU_FinishAtCurrent.source_view
#print axioms NJU_FinishCaller.reached
#print axioms NJU_FinishCase.current
#print axioms NJU_FinishCore.selected
#print axioms NJU_FinishCore.reached
#print axioms NJU_FinishCore.source
#print axioms NJU_FinishDomain.reached
#print axioms AspisR1.NJU_FinishInput.intrinsic
#print axioms AspisR1.NJU_FinishInput.of_original
#print axioms NJU_FinishInstall.at_call
#print axioms NJU_FinishObserved.bind_ext
#print axioms NJU_FinishObserved.skeleton
#print axioms NJU_FinishObserved.source
#print axioms AspisR1.NJU_GeneralFinishRoot.finish
#print axioms AspisR1.NJU_GeneralFinishRoot.ported
#print axioms NJU_Log.erase_bind
#print axioms NJU_Log.erase_pure
#print axioms NJU_Log.erase_lift
#print axioms NJU_Log.erase_liftM
#print axioms NJU_Log.erase_record
#print axioms NJU_Log.erase_if
#print axioms NJU_Log.erase_flow
#print axioms NJU_Log.prod_cases
#print axioms NJU_Log.fail_prefix
#print axioms NJU_Log.div_prefix
#print axioms NJU_ResumeErase.finishTail
#print axioms NJU_ResumeErase.queryEnd
#print axioms NJU_ResumeErase.queryMid
#print axioms NJU_ResumeErase.queryBlock
#print axioms NJU_ResumeErase.resumeBody
#print axioms NJU_ResumeErase.header
#print axioms NJU_ResumeReference.source
#print axioms NJU_ResumeRoot.source
#print axioms NJU_ResumeRoot.cohort
#print axioms NJU_ViewWindows.entered_size
#print axioms NJU_ViewWindows.lengths
#print axioms NJU_ViewWindows.bad_current
#print axioms AspisR1.NJU_WeakAlignAfterPhase.trace
#print axioms AspisR1.NJU_WeakAlignAllocatorPhase.trace
#print axioms AspisR1.NJU_WeakAlignAllocatorPhase.source
#print axioms AspisR1.NJU_WeakAlignPairPhase.certificate
#print axioms AspisR1.NJU_WeakAlignPairPhaseSource.source
#print axioms AspisR1.NJU_WeakAlignRegularPhase.trace
#print axioms AspisR1.NJU_WeakAlignRegularPhaseSource.source
#print axioms AspisR1.NJU_WeakAlignRegularPhaseSource.frames
#print axioms AspisR1.NJU_WeakAlignSharedPhase.trace
#print axioms AspisR1.NJU_WeakAllocatorChain.interpreted
#print axioms AspisR1.NJU_WeakAllocatorChain.complete
#print axioms AspisR1.NJU_WeakAllocatorInstantiation.source
#print axioms AspisR1.NJU_WeakFinishComposedLog.source
#print axioms AspisR1.NJU_WeakFinishObserved.detail_source
#print axioms AspisR1.NJU_WeakFinishObserved.source
#print axioms AspisR1.NJU_WeakFinishObserved.source_log
#print axioms AspisR1.NJU_WeakFinishPairCertificate.observe_bound
#print axioms AspisR1.NJU_WeakFinishPairCertificate.source
#print axioms AspisR1.NJU_WeakFinishPort.source
#print axioms AspisR1.NJU_WeakPairCaller.alphas
#print axioms AspisR1.NJU_WeakPairCaller.new_owner
#print axioms AspisR1.NJU_WeakPairCaller.caller
#print axioms AspisR1.NJU_WeakPairDomain.of_original
#print axioms AspisR1.NJU_WeakPairInstalled.source
#print axioms AspisR1.NJU_WeakPairInstantiation.source
#print axioms AspisR1.NJU_WeakPairInstantiation.root
#print axioms AspisR1.NJU_WeakRegularChain.after_interpreted
#print axioms AspisR1.NJU_WeakRegularChain.after_exists
#print axioms AspisR1.NJU_WeakRegularChain.interpreted
#print axioms AspisR1.NJU_WeakRegularChain.complete
#print axioms AspisR1.NJU_WeakRegularContinuation.source
#print axioms AspisR1.NJU_WeakSharedChain.shared_interpreted
#print axioms AspisR1.NJU_WeakSharedComplete.complete
#print axioms NJU_ResumeObserved.run
#print axioms NJU_ResumeObserved.runRef
#print axioms AspisR1.NJF_Root.finish
#print axioms AspisR1.RPx_Deployed.deployed

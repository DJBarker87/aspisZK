import NKH_COMBINED_IMPORT
import NJU_COMBINED_IMPORT
import NKK_AllocationBind
import NKK_AllocationStage
import NKK_AllocationWidth
import NKK_ClauseRoot
import NKK_Clauses
import NKK_ClausesFinishTail
import NKK_ClausesQueryBlock
import NKK_ClausesQueryEnd
import NKK_ClausesQueryMid
import NKK_ClausesResumeBody
import NKK_ClausesRun
import NKK_CloseTail
import NKK_Compare
import NKK_DecoderDomain
import NKK_DigestChain
import NKK_DigestCut
import NKK_DigestSource
import NKK_EmbedRaw
import NKK_FieldAssociation
import NKK_FieldCps
import NKK_FieldDomain
import NKK_FieldFold
import NKK_FieldLiteral
import NKK_FieldShape
import NKK_FieldSites
import NKK_FieldStages
import NKK_HeaderFactor
import NKK_HeaderSource
import NKK_Invoke
import NKK_LogAlgebra
import NKK_LogClauses
import NKK_LogReduce
import NKK_NativeRaw
import NKK_QueryStage
import NKK_RawAssociation
import NKK_RawChain
import NKK_RawCps
import NKK_RawFold
import NKK_RawLength
import NKK_RawPrefix
import NKK_RawResult
import NKK_RawSlots
import NKK_RawSynchrony
import NKK_ReadFrames
import NKK_ResumeBodyFactor
import NKK_RootStatements
import NKK_RunEval
import NKK_SectionFrames
import NKK_Try
import NKK_ZStage
#print axioms NKK_AllocationBind.rejected
#print axioms NKK_AllocationStage.events
#print axioms NKK_AllocationStage.rejected
#print axioms NKK_AllocationStage.width
#print axioms NKK_ClauseRoot.source
#print axioms NKK_ClauseRoot.cohort
#print axioms NKK_Clauses.raw
#print axioms NKK_Clauses.k
#print axioms NKK_Clauses.e
#print axioms NKK_Clauses.semantic
#print axioms NKK_Clauses.weights
#print axioms NKK_Clauses.validate
#print axioms NKK_Clauses.filled
#print axioms NKK_Clauses.headerAny
#print axioms NKK_Clauses.digest
#print axioms NKK_ResumeClauses.finishTail
#print axioms NKK_ResumeClauses.queryBlock
#print axioms NKK_ResumeClauses.queryEnd
#print axioms NKK_ResumeClauses.queryMid
#print axioms NKK_ResumeClauses.resumeBody
#print axioms NKK_ResumeClauses.run
#print axioms NKK_Compare.list_result
#print axioms NKK_Compare.eq_result
#print axioms NKK_Compare.ne_result
#print axioms NKK_Compare.branch
#print axioms NKK_DecoderDomain.e
#print axioms NKK_DecoderDomain.k
#print axioms NKK_DigestChain.source_eq_model
#print axioms NKK_DigestCut.same_call
#print axioms NKK_DigestCut.byte_frame
#print axioms NKK_DigestSource.source_eq_model
#print axioms NKK_EmbedRaw.result
#print axioms NKK_EmbedRaw.pure
#print axioms NKK_EmbedRaw.bind
#print axioms NKK_EmbedRaw.record
#print axioms NKK_EmbedRaw.raw
#print axioms NKK_FieldFold.association
#print axioms NKK_FieldCps.map_cont
#print axioms NKK_FieldCps.source
#print axioms NKK_FieldDomain.bounded
#print axioms NKK_FieldDomain.inside
#print axioms NKK_FieldFold.error_prefix
#print axioms NKK_FieldFold.abort_prefix
#print axioms NKK_FieldFold.div_prefix
#print axioms NKK_FieldLiteral.call_k
#print axioms NKK_FieldLiteral.call_e
#print axioms NKK_FieldLiteral.source
#print axioms NKK_FieldShape.call_tag
#print axioms NKK_FieldShape.shape
#print axioms NKK_FieldSites.gamma
#print axioms NKK_FieldSites.z
#print axioms NKK_FieldSites.gamma_fold
#print axioms NKK_FieldSites.z_fold
#print axioms NKK_FieldStages.gamma_source
#print axioms NKK_HeaderFactor.source
#print axioms NKK_Invoke.bind
#print axioms NKK_Invoke.abort
#print axioms NKK_Invoke.diverges
#print axioms NKK_LogAlgebra.bind_congr
#print axioms NKK_LogAlgebra.bind_assoc
#print axioms NKK_LogClauses.pure
#print axioms NKK_LogClauses.lift
#print axioms NKK_LogClauses.liftM
#print axioms NKK_LogClauses.record
#print axioms NKK_LogClauses.bind
#print axioms NKK_LogClauses.branch
#print axioms NKK_LogClauses.flow
#print axioms NKK_LogReduce.pure_bind
#print axioms NKK_LogReduce.lift_ok_bind
#print axioms NKK_LogReduce.liftM_ok_bind
#print axioms NKK_NativeRaw.backing
#print axioms NKK_NativeRaw.advance
#print axioms NKK_NativeRaw.one
#print axioms NKK_QueryStage.stage8
#print axioms NKK_QueryStage.stage6
#print axioms NKK_RawFold.association
#print axioms NKK_NativeRaw.read_chain
#print axioms NKK_NativeRaw.read_result
#print axioms NKK_RawCps.source
#print axioms NKK_RawFold.fold_nil
#print axioms NKK_RawFold.fold_cons
#print axioms NKK_RawFold.fail_stays
#print axioms NKK_RawFold.div_stays
#print axioms NKK_RawFold.length
#print axioms NKK_RawPrefix.source
#print axioms NKK_RawPrefix.associated
#print axioms NKK_RawResult.source
#print axioms NKK_RawSlots.query8
#print axioms NKK_RawSlots.query6
#print axioms NKK_RawSlots.roots
#print axioms NKK_RawFold.clauses
#print axioms NKK_RawFold.synchronized
#print axioms NKK_ReadFrames.k
#print axioms NKK_ReadFrames.e
#print axioms NKK_ResumeBodyFactor.source
#print axioms NKK_RunEval.bind_eq
#print axioms NKK_RunEval.pure_eq
#print axioms NKK_SectionFrames.semantic
#print axioms NKK_SectionFrames.weights
#print axioms NKK_Try.branch
#print axioms NKK_ZStage.source_eq_model
#print axioms NJU_ResumeRoot.source
#print axioms NJU_ResumeRoot.cohort
#print axioms AspisR1.RPx_Deployed.deployed

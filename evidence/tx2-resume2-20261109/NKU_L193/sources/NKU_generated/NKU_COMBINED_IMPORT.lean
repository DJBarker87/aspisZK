import NKN_COMBINED_IMPORT
import NKK_COMBINED_IMPORT
import NKU_AfterZ
import NKU_AfterZSource
import NKU_Allocation
import NKU_Array22
import NKU_BodyJoin
import NKU_CallerScope
import NKU_Chronology
import NKU_Core
import NKU_DigestBody
import NKU_DigestCheckpoint
import NKU_DigestCheckpointFrame
import NKU_DigestJoin
import NKU_DigestProof
import NKU_DigestProofFrame
import NKU_DigestPublic
import NKU_DigestPublicFrame
import NKU_DigestState
import NKU_EAt
import NKU_EndArithmetic
import NKU_FineDigestJoin
import NKU_FineFirstJoin
import NKU_FineGamma
import NKU_FineGammaJoin
import NKU_FineHeader
import NKU_FineLastJoin
import NKU_FineMiddleJoin
import NKU_FineQueryEnd
import NKU_FineQueryFirst
import NKU_FineQueryMid
import NKU_FineRead
import NKU_FineRoot
import NKU_FineRoots
import NKU_FineRootsJoin
import NKU_FineSemanticJoin
import NKU_FineWords
import NKU_FineZ
import NKU_FineZJoin
import NKU_FinishFactor
import NKU_FinishTransport
import NKU_Fold
import NKU_Front
import NKU_Gamma
import NKU_GammaJoin
import NKU_GammaPack
import NKU_HeaderDomain
import NKU_HeaderEnd
import NKU_HeaderPrefix
import NKU_HeaderSize
import NKU_HeaderSlots
import NKU_HeaderState
import NKU_HeaderStep
import NKU_HeaderTailEnd
import NKU_HeaderValue
import NKU_InputAt
import NKU_KAt
import NKU_MixedFrame
import NKU_Offsets
import NKU_Pack
import NKU_ParentFold
import NKU_QueryEnd
import NKU_QueryFirst
import NKU_QueryFirstJoin
import NKU_QueryJoin
import NKU_QueryLastJoin
import NKU_QueryMid
import NKU_QueryMiddleJoin
import NKU_QueryPack
import NKU_RawAt
import NKU_ResumeRoot
import NKU_RootPack
import NKU_Roots
import NKU_Semantic
import NKU_SemanticJoin
import NKU_SemanticSource
import NKU_SourceConstructors
import NKU_State
import NKU_Success
import NKU_Tail
import NKU_TailSource
import NKU_TerminalCut
import NKU_Validator
import NKU_Weights
import NKU_WordsAt
import NKU_ZClaim
import NKU_ZJoin
import NKU_ZSource
#print axioms NKU_AfterZ.source
#print axioms NKU_Allocation.rejected
#print axioms NKU_Allocation.frame
#print axioms NKU_Array22.source
#print axioms NKU_BodyJoin.source
#print axioms NKU_Chronology.next
#print axioms NKU_Chronology.reject
#print axioms NKU_Chronology.abort
#print axioms NKU_Chronology.diverge
#print axioms NKU_DigestBody.source
#print axioms NKU_DigestCheckpoint.source_eq_run
#print axioms NKU_DigestJoin.source
#print axioms NKU_DigestProof.source_eq_run
#print axioms NKU_DigestProof.frame
#print axioms NKU_DigestPublic.source_eq_run
#print axioms NKU_DigestPublic.frame
#print axioms NKU_EndArithmetic.wrap
#print axioms NKU_FineDigestJoin.installed
#print axioms NKU_FineFirstJoin.installed
#print axioms NKU_FineGamma.installed
#print axioms NKU_FineGammaJoin.installed
#print axioms NKU_FineLastJoin.installed
#print axioms NKU_FineMiddleJoin.installed
#print axioms NKU_FineQueryEnd.installed
#print axioms NKU_FineQueryFirst.installed
#print axioms NKU_FineQueryMid.installed
#print axioms NKU_FineRead.e_bind
#print axioms NKU_FineRead.k_bind
#print axioms NKU_FineRead.raw_bind
#print axioms NKU_FineRoot.suffix
#print axioms NKU_FineRoot.installed
#print axioms NKU_FineRoot.source
#print axioms NKU_FineRoot.cohort
#print axioms NKU_FineRoots.installed
#print axioms NKU_FineRootsJoin.installed
#print axioms NKU_FineSemanticJoin.installed
#print axioms NKU_FineWords.installed
#print axioms NKU_FineZ.installed
#print axioms NKU_FineZJoin.installed
#print axioms NKU_FinishFactor.source
#print axioms NKU_FinishTransport.source
#print axioms NKU_Front.suffix_eq
#print axioms NKU_Front.source
#print axioms NKU_Gamma.source_eq_run
#print axioms NKU_Gamma.frame
#print axioms NKU_GammaJoin.source
#print axioms NKU_GammaPack.frame
#print axioms NKU_HeaderDomain.wrong_length
#print axioms NKU_HeaderDomain.length
#print axioms NKU_HeaderEnd.fixed
#print axioms NKU_HeaderEnd.returned
#print axioms NKU_HeaderPrefix.source
#print axioms NKU_HeaderSize.size
#print axioms NKU_HeaderSlots.same
#print axioms NKU_HeaderStep.source
#print axioms NKU_HeaderTailEnd.fixed
#print axioms NKU_HeaderValue.source
#print axioms NKU_MixedFrame.frame
#print axioms NKU_Offsets.gamma
#print axioms NKU_Offsets.z
#print axioms NKU_Offsets.semantic
#print axioms NKU_Offsets.weights
#print axioms NKU_Pack.frame
#print axioms NKU_QueryEnd.source_eq_run
#print axioms NKU_QueryEnd.frame
#print axioms NKU_QueryFirst.source_eq_run
#print axioms NKU_QueryFirst.frame
#print axioms NKU_QueryFirstJoin.source
#print axioms NKU_QueryJoin.source
#print axioms NKU_QueryLastJoin.source
#print axioms NKU_QueryMid.source_eq_run
#print axioms NKU_QueryMid.frame
#print axioms NKU_QueryMiddleJoin.source
#print axioms NKU_ResumeRoot.suffix_eq
#print axioms NKU_ResumeRoot.source
#print axioms NKU_ResumeRoot.clauses
#print axioms NKU_ResumeRoot.cohort
#print axioms NKU_RootPack.frame
#print axioms NKU_Roots.source_eq_run
#print axioms NKU_Roots.frame
#print axioms NKU_Semantic.frame
#print axioms NKU_SemanticJoin.source
#print axioms NKU_SourceConstructors.point
#print axioms NKU_SourceConstructors.prepared
#print axioms NKU_SourceConstructors.accumulator
#print axioms NKU_SourceConstructors.pair
#print axioms NKU.header_frame
#print axioms NKU_Success.bind
#print axioms NKU_Success.pure
#print axioms NKU_Success.reject
#print axioms NKU_Tail.guard_reject
#print axioms NKU_TailSource.source
#print axioms NKU_TerminalCut.pair
#print axioms NKU_Validator.frame
#print axioms NKU_Weights.frame
#print axioms NKU_ZClaim.source_eq_run
#print axioms NKU_ZClaim.frame
#print axioms NKU_ZJoin.source
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms NKU_CallerScope.header_to_roots
#print axioms NKU_CallerScope.first_queries
#print axioms NKU_CallerScope.middle_queries
#print axioms NKU_CallerScope.last_queries
#print axioms NKU_Core.bind
#print axioms NKU_DigestCheckpointFrame.preserved
#print axioms NKU_DigestProofFrame.preserved
#print axioms NKU_DigestPublicFrame.preserved
#print axioms NKU_DigestState.preserved
#print axioms NKU_EAt.returned
#print axioms NKU_EAt.domain
#print axioms NKU_FineHeader.installed
#print axioms NKU_HeaderState.returned
#print axioms NKU_HeaderState.root_entry
#print axioms NKU_InputAt.bound
#print axioms NKU_InputAt.initial
#print axioms NKU_KAt.returned
#print axioms NKU_KAt.domain
#print axioms NKU_ParentFold.installed
#print axioms NKU_ParentFold.source
#print axioms NKU_ParentFold.cohort
#print axioms NKU_ParentFold.clauses
#print axioms NKU_RawAt.total
#print axioms NKU_RawAt.domain
#print axioms NKU_WordsAt.total

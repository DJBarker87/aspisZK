import F3K_AbsorbCode
import F3K_ArrayFacts
import F3K_ArrayValues
import F3K_CheckpointPreparedFields
import F3K_CheckpointQueryNumeric
import F3K_CheckpointQuerySource
import F3K_CodeBind
import F3K_CodePure
import F3K_CodeStep
import F3K_ConcreteDecode
import F3K_ContextFinalState
import F3K_InactiveCodec
import F3K_InactivePhysical
import F3K_InputFinalState
import F3K_LimbBytes
import F3K_NativeProtocol33
import F3K_NativeQuery33
import F3K_NativeSampler33
import F3K_OpeningCalls
import F3K_OpeningFirst4
import F3K_OpeningFromSource
import F3K_OpeningLast2
import F3K_OpeningPair27
import F3K_OpeningPair29
import F3K_OpeningQuery
import F3K_OpeningSpine
import F3K_OpeningSuffix
import F3K_OuterPrepareSplice
import F3K_PayloadFits
import F3K_PrepareLog
import F3K_PreparedInput33
import F3K_PreparedInputQuery
import F3K_PreparedSourceFields
import F3K_ProtocolProjection
import F3K_QueryAddress
import F3K_QueryChain
import F3K_QueryCode
import F3K_QueryDecoderSource
import F3K_QueryDriverModel
import F3K_QueryFull
import F3K_QueryIndex
import F3K_QueryLog
import F3K_QueryOne
import F3K_QueryRowOutput
import F3K_QuerySamplerOutput
import F3K_QueryScanCall
import F3K_QueryScanLast
import F3K_QueryScanStep
import F3K_QueryValues
import F3K_QueryWords
import F3K_RhoJoin
import F3K_RhoOne
import F3K_SamplerIndex
import F3K_SamplerOne
import F3K_SamplerProtocol
import F3K_ScalarJoin
import F3K_ScalarOne
import F3K_SourceQueryDecode
import F3K_WideEncoding
import F3K_WordCodec

#print axioms AspisR1.F3K_AbsorbCode.run_absorb
#print axioms AspisR1.F3K_ArrayFacts.updated
#print axioms AspisR1.F3K_ArrayFacts.mutated
#print axioms AspisR1.F3K_ArrayValues.updated
#print axioms AspisR1.F3K_ArrayValues.mutated
#print axioms AspisR1.F3K_CheckpointPreparedFields.variant
#print axioms AspisR1.F3K_CheckpointPreparedFields.queries
#print axioms AspisR1.F3K_CheckpointPreparedFields.state
#print axioms AspisR1.F3K_CheckpointQueryNumeric.exact_queries
#print axioms AspisR1.F3K_CheckpointQuerySource.source
#print axioms AspisR1.F3K_CodeBind.success
#print axioms AspisR1.F3K_CodeBind.pair_success
#print axioms AspisR1.F3K_CodeBind.lifted_empty
#print axioms AspisR1.F3K_CodePure.invert
#print axioms AspisR1.F3K_CodeStep.lift_success
#print axioms AspisR1.F3K_CodeStep.pure_step
#print axioms AspisR1.F3K_CodeStep.digest_success
#print axioms AspisR1.F3K_CodeStep.absorb
#print axioms AspisR1.F3K_ConcreteDecode.accepted
#print axioms AspisR1.F3K_ContextFinalState.input
#print axioms AspisR1.F3K_InactiveCodec.source_roundtrip
#print axioms AspisR1.F3K_InactivePhysical.bytes
#print axioms AspisR1.F3K_InactivePhysical.row
#print axioms AspisR1.F3K_InputFinalState.fields
#print axioms AspisR1.F3K_LimbBytes.source_list
#print axioms AspisR1.F3K_LimbBytes.decoded_list
#print axioms AspisR1.F3K_LimbBytes.canonical_limb
#print axioms AspisR1.F3K_NativeProtocol33.native
#print axioms AspisR1.F3K_NativeQuery33.native
#print axioms AspisR1.F3K_NativeSampler33.native
#print axioms AspisR1.F3K_OpeningFirst4.sampler
#print axioms AspisR1.F3K_OpeningFromSource.from_double
#print axioms AspisR1.F3K_OpeningLast2.sampler
#print axioms AspisR1.F3K_OpeningPair27.sampler
#print axioms AspisR1.F3K_OpeningPair29.sampler
#print axioms AspisR1.F3K_OpeningQuery.queries
#print axioms AspisR1.F3K_OpeningQuery.decoded
#print axioms AspisR1.F3K_OpeningSpine.from_double
#print axioms AspisR1.F3K_OpeningSuffix.sampler
#print axioms AspisR1.F3K_OuterPrepareSplice.reached
#print axioms AspisR1.F3K_PayloadFits.fits
#print axioms AspisR1.F3K_PrepareLog.spine
#print axioms AspisR1.F3K_PreparedInput33.from_cut
#print axioms AspisR1.F3K_PreparedInputQuery.from_cut
#print axioms AspisR1.F3K_PreparedSourceFields.fields
#print axioms AspisR1.F3K_PreparedSourceFields.query_binding
#print axioms AspisR1.F3K_ProtocolProjection.source
#print axioms AspisR1.F3K_QueryAddress.address
#print axioms AspisR1.F3K_QueryChain.chain
#print axioms AspisR1.F3K_QueryCode.observed
#print axioms AspisR1.F3K_QueryDecoderSource.source
#print axioms AspisR1.F3K_QueryDriverModel.driver
#print axioms AspisR1.F3K_QueryFull.exact_row
#print axioms AspisR1.F3K_QueryIndex.drop_index
#print axioms AspisR1.F3K_QueryIndex.drop_decoded
#print axioms AspisR1.F3K_QueryLog.ordered
#print axioms AspisR1.F3K_QueryOne.sampler
#print axioms AspisR1.F3K_QueryRowOutput.output
#print axioms AspisR1.F3K_QuerySamplerOutput.output
#print axioms AspisR1.F3K_QueryScanCall.scan
#print axioms AspisR1.F3K_QueryScanCall.finish
#print axioms AspisR1.F3K_QueryScanLast.last
#print axioms AspisR1.F3K_QueryScanStep.index_exists
#print axioms AspisR1.F3K_QueryScanStep.more
#print axioms AspisR1.F3K_QueryScanStep.stop
#print axioms AspisR1.F3K_QueryScanStep.progress
#print axioms AspisR1.F3K_QueryValues.lengths
#print axioms AspisR1.F3K_QueryValues.pairs
#print axioms AspisR1.F3K_QueryValues.deterministic
#print axioms AspisR1.F3K_QueryWords.word
#print axioms AspisR1.F3K_QueryWords.mask
#print axioms AspisR1.F3K_QueryWords.decoded
#print axioms AspisR1.F3K_RhoJoin.rho
#print axioms AspisR1.F3K_RhoOne.rho
#print axioms AspisR1.F3K_SamplerIndex.old_index
#print axioms AspisR1.F3K_SamplerIndex.first_entry
#print axioms AspisR1.F3K_SamplerOne.state
#print axioms AspisR1.F3K_SamplerOne.one
#print axioms AspisR1.F3K_SamplerProtocol.exact_run
#print axioms AspisR1.F3K_SamplerProtocol.initial
#print axioms AspisR1.F3K_ScalarJoin.scalar
#print axioms AspisR1.F3K_ScalarOne.scalar
#print axioms AspisR1.F3K_SourceQueryDecode.concrete
#print axioms AspisR1.F3K_SourceQueryDecode.source
#print axioms AspisR1.F3K_WideEncoding.encoding
#print axioms AspisR1.F3K_WordCodec.carrier
#print axioms AspisR1.F3K_WordCodec.encoded_list
#print axioms AspisR1.F3K_WordCodec.roundtrip
#print axioms AspisR1.F3K_WordCodec.encoding

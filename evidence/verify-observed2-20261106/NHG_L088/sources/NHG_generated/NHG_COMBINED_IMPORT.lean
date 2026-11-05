import NGK_COMBINED_IMPORT
import NGX_COMBINED_IMPORT
import NHG_Serializer
import NHG_PublicTranscript
import NHG_Lengths
import NHG_CopyFrame
import NHG_FieldSpec
import NHG_Semantic
import NHG_Begin13
import NHG_Begin9
import NHG_Begin5
import NHG_Begin
import NHG_FieldBounds
import NHG_FrontierFrame
import NHG_FrontierPackets
import NHG_PublicCarrier
import NHG_StdBytes
import NHG_ProducerDomains
import NHG_ProducerWidths
import NHG_ProducerPackets
import NHG_ProgramChain
import NHG_AppendFrame
import NHG_SnapshotViews
import NHG_BeginFrame
import NHG_Product
import NHG_FrontComposition
import NHG_FinishLeaves
import NHG_SelectedClaim
import NHG_AddWords
import NHG_ExtraLeaves
import NHG_ClaimsDomain
#print axioms AspisR1.NHG_Serializer.restore_map
#print axioms AspisR1.NHG_Serializer.source
#print axioms AspisR1.NHG_Serializer.bytes
#print axioms AspisR1.NHG_Serializer.field_body
#print axioms AspisR1.NHG_PublicTranscript.source
#print axioms AspisR1.NHG_PublicTranscript.code
#print axioms AspisR1.NHG_Lengths.digest
#print axioms AspisR1.NHG_Lengths.index
#print axioms AspisR1.NHG_Lengths.source
#print axioms AspisR1.NHG_Lengths.bound
#print axioms AspisR1.NHG_Lengths.returned
#print axioms AspisR1.NHG_Lengths.prefix_room
#print axioms AspisR1.NHG_Lengths.digest_domain
#print axioms AspisR1.NHG_CopyFrame.step
#print axioms AspisR1.NHG_CopyFrame.realloc_initialized
#print axioms AspisR1.NHG_CopyFrame.grow_append4
#print axioms AspisR1.NHG_FieldSpec.status_injective
#print axioms AspisR1.NHG_FieldSpec.source
#print axioms AspisR1.NHG_FieldSpec.reject
#print axioms AspisR1.NHG_Semantic.transfer
#print axioms AspisR1.NHG_Semantic.withdrawal
#print axioms AspisR1.NHG_Semantic.source
#print axioms AspisR1.NHG_Semantic.transition
#print axioms AspisR1.NHG_Begin13.source
#print axioms AspisR1.NHG_Begin9.source
#print axioms AspisR1.NHG_Begin5.source
#print axioms AspisR1.NHG_Begin.source
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NHG_FieldBounds.raw_length
#print axioms AspisR1.NHG_FieldBounds.raw_prefix
#print axioms AspisR1.NHG_FieldBounds.source
#print axioms AspisR1.NHG_FrontierFrame.envelope
#print axioms AspisR1.NHG_FrontierFrame.map_chain
#print axioms AspisR1.NHG_FrontierFrame.map_injective
#print axioms AspisR1.NHG_FrontierFrame.source
#print axioms AspisR1.NHG_FrontierFrame.row_length
#print axioms AspisR1.NHG_FrontierFrame.row_count
#print axioms AspisR1.NHG_FrontierFrame.stage_domain
#print axioms AspisR1.NHG_FrontierFrame.frontier_envelope
#print axioms AspisR1.NHG_FrontierPackets.transport
#print axioms AspisR1.NHG_FrontierPackets.row_widths
#print axioms AspisR1.NHG_FrontierPackets.source
#print axioms AspisR1.NHG_FrontierPackets.closed_packets
#print axioms AspisR1.NHG_PublicCarrier.same_execution
#print axioms AspisR1.NHG_PublicCarrier.new_carrier
#print axioms AspisR1.NHG_PublicCarrier.begin_carrier
#print axioms AspisR1.NHG_StdBytes.push
#print axioms AspisR1.NHG_StdBytes.index
#print axioms AspisR1.NHG_ProducerDomains.first
#print axioms AspisR1.NHG_ProducerDomains.prefix_nonempty
#print axioms AspisR1.NHG_ProducerDomains.words_noninitial
#print axioms AspisR1.NHG_ProducerDomains.frontier_noninitial
#print axioms AspisR1.NHG_ProducerDomains.words_room
#print axioms AspisR1.NHG_ProducerDomains.frontier_room
#print axioms AspisR1.NHG_ProducerWidths.single_width
#print axioms AspisR1.NHG_ProducerWidths.widths
#print axioms AspisR1.NHG_ProducerWidths.fields
#print axioms AspisR1.NHG_ProducerWidths.field_domain
#print axioms AspisR1.NHG_ProducerWidths.frontier_domain
#print axioms AspisR1.NHG_ProducerPackets.emitted
#print axioms AspisR1.NHG_ProducerPackets.source
#print axioms AspisR1.NHG_ProgramChain.append
#print axioms AspisR1.NHG_ProgramChain.history_bytes
#print axioms AspisR1.NHG_ProgramChain.reached_field
#print axioms AspisR1.NHG_ProgramChain.reached_frontier
#print axioms AspisR1.NHG_AppendFrame.grow_append
#print axioms AspisR1.NHG_AppendFrame.old_prefix
#print axioms AspisR1.NHG_AppendFrame.new_suffix
#print axioms AspisR1.NHG_SnapshotViews.actual
#print axioms AspisR1.NHG_SnapshotViews.carrier
#print axioms AspisR1.NHG_SnapshotViews.array_ext
#print axioms AspisR1.NHG_SnapshotViews.frontier_ext
#print axioms AspisR1.NHG_BeginFrame.result
#print axioms AspisR1.NHG_BeginFrame.effects
#print axioms AspisR1.NHG_BeginFrame.composed
#print axioms AspisR1.NHG_Product.words
#print axioms AspisR1.NHG_Product.returns
#print axioms AspisR1.NHG_Product.canonical
#print axioms AspisR1.NHG_Product.natural
#print axioms AspisR1.NHG_FrontComposition.bind_congr
#print axioms AspisR1.NHG_FrontComposition.staged
#print axioms AspisR1.NHG_FinishLeaves.boundary_step
#print axioms AspisR1.NHG_FinishLeaves.boundary_seed
#print axioms AspisR1.NHG_FinishLeaves.boundary_result
#print axioms AspisR1.NHG_FinishLeaves.value_step
#print axioms AspisR1.NHG_FinishLeaves.value_seed
#print axioms AspisR1.NHG_FinishLeaves.value_result
#print axioms AspisR1.NHG_FinishLeaves.product_packet
#print axioms AspisR1.NHG_FinishLeaves.value_packet_step
#print axioms AspisR1.NHG_SelectedClaim.source
#print axioms AspisR1.NHG_SelectedClaim.range
#print axioms AspisR1.NHG_SelectedClaim.returned
#print axioms AspisR1.NHG_AddWords.cases_mod
#print axioms AspisR1.NHG_AddWords.generated
#print axioms AspisR1.NHG_AddWords.nq_add
#print axioms AspisR1.NHG_AddWords.nq_mul
#print axioms AspisR1.NHG_ExtraLeaves.scalar_source
#print axioms AspisR1.NHG_ExtraLeaves.carry_total
#print axioms AspisR1.NHG_ExtraLeaves.carry_result
#print axioms AspisR1.NHG_ExtraLeaves.empty_source
#print axioms AspisR1.NHG_ExtraLeaves.scalar_total
#print axioms AspisR1.NHG_ExtraLeaves.initial_source
#print axioms AspisR1.NHG_ExtraLeaves.reconstruct_step
#print axioms AspisR1.NHG_ExtraLeaves.reconstruct_result
#print axioms AspisR1.NHG_ExtraLeaves.sum_result
#print axioms AspisR1.NHG_ExtraLeaves.factor_source
#print axioms AspisR1.NHG_ExtraLeaves.equality_result
#print axioms AspisR1.NHG_ClaimsDomain.requests
#print axioms AspisR1.NHG_ClaimsDomain.row_copy
#print axioms AspisR1.NHG_ClaimsDomain.payload_length
#print axioms AspisR1.NHG_ClaimsDomain.round_width
#print axioms AspisR1.NHG_ClaimsDomain.fixed_widths

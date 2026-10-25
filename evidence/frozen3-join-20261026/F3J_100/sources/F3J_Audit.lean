import F3J_BlockCalls
import F3J_BlockCode
import F3J_BlockCodeValue
import F3J_BlockSampler
import F3J_CheckpointSource
import F3J_CircleCode
import F3J_CircleJoin
import F3J_CirclePair
import F3J_First25
import F3J_First27
import F3J_InitialLog
import F3J_InitialValue
import F3J_InputRows
import F3J_LengthFrame
import F3J_NativeConstruction
import F3J_NativeInput
import F3J_NativePrefix
import F3J_NativePrefix27
import F3J_Nonvacuity
import F3J_OpeningCode
import F3J_OpeningFacts
import F3J_OpeningFrame
import F3J_OpeningJoin
import F3J_OpeningPayloads
import F3J_OpeningSampler
import F3J_PhysicalQuery
import F3J_PositiveTrace
import F3J_PrefixWitness
import F3J_PreparedInput
import F3J_PreparedInput27
import F3J_Public
import F3J_QueryAbsorber
import F3J_QueryJoin
import F3J_QueryLog
import F3J_QueryNonvacuity
import F3J_QueryPairs
import F3J_QueryRow
import F3J_QuerySelection
import F3J_QuerySource
import F3J_RecordPayload
import F3J_ReseedSampler
import F3J_ReseedSource
import F3J_RowBindings
import F3J_RunState
import F3J_SamplerCompose
import F3J_SamplerRun
import F3J_SamplerStep
import F3J_SamplerStructure
import F3J_ScalarCode
import F3J_SemanticLog
import F3J_SemanticPrefix
import F3J_SemanticValue
import F3J_SourceBlock
import F3J_SourceBlockValue
import F3J_ValidatedLog
set_option autoImplicit false

-- Final declarations audit only; no package or manifest replay.
#check AspisR1.F3J_NativeConstruction.native
#check AspisR1.F3J_NativePrefix27.native
#check AspisR1.F3J_PhysicalQuery.ordered
#check AspisR1.F3J_CheckpointSource.stage

#print axioms AspisR1.F3J_BlockCalls.from_success
#print axioms AspisR1.F3J_BlockCalls.consistent
#print axioms AspisR1.F3J_BlockCode.sample
#print axioms AspisR1.F3J_BlockCodeValue.returned
#print axioms AspisR1.F3J_BlockSampler.payload
#print axioms AspisR1.F3J_CheckpointSource.stage
#print axioms AspisR1.F3J_CircleCode.first
#print axioms AspisR1.F3J_CircleCode.second
#print axioms AspisR1.F3J_CircleJoin.first
#print axioms AspisR1.F3J_CircleJoin.second
#print axioms AspisR1.F3J_CirclePair.sampler
#print axioms AspisR1.F3J_First25.sampler
#print axioms AspisR1.F3J_First27.sampler
#print axioms AspisR1.F3J_InitialLog.initial
#print axioms AspisR1.F3J_InitialValue.initial
#print axioms AspisR1.F3J_InputRows.erased
#print axioms AspisR1.F3J_InputRows.valid
#print axioms AspisR1.F3J_LengthFrame.cast_length
#print axioms AspisR1.F3J_LengthFrame.framed
#print axioms AspisR1.F3J_NativeConstruction.native
#print axioms AspisR1.F3J_NativeInput.from_cut
#print axioms AspisR1.F3J_NativePrefix.native
#print axioms AspisR1.F3J_NativePrefix27.native
#print axioms AspisR1.F3J_Nonvacuity.backend
#print axioms AspisR1.F3J_Nonvacuity.sample
#print axioms AspisR1.F3J_Nonvacuity.issued
#print axioms AspisR1.F3J_OpeningCode.block
#print axioms AspisR1.F3J_OpeningFacts.from_success
#print axioms AspisR1.F3J_OpeningFacts.consistent
#print axioms AspisR1.F3J_OpeningFrame.absorb
#print axioms AspisR1.F3J_OpeningJoin.block
#print axioms AspisR1.F3J_OpeningPayloads.selected
#print axioms AspisR1.F3J_OpeningSampler.payload
#print axioms AspisR1.F3J_PhysicalQuery.ordered
#print axioms AspisR1.F3J_PositiveTrace.exact_trace
#print axioms AspisR1.F3J_PrefixWitness.pack
#print axioms AspisR1.F3J_PrefixWitness.through
#print axioms AspisR1.F3J_PrefixWitness.carried_statement
#print axioms AspisR1.F3J_PreparedInput.from_cut
#print axioms AspisR1.F3J_PreparedInput27.from_cut
#print axioms AspisR1.F3J_Public.from_cut
#print axioms AspisR1.F3J_QueryAbsorber.ordered
#print axioms AspisR1.F3J_QueryJoin.ordered
#print axioms AspisR1.F3J_QueryLog.chain
#print axioms AspisR1.F3J_QueryLog.length
#print axioms AspisR1.F3J_QueryLog.sampler
#print axioms AspisR1.F3J_QueryNonvacuity.pairs
#print axioms AspisR1.F3J_QueryNonvacuity.length
#print axioms AspisR1.F3J_QueryPairs.ordered
#print axioms AspisR1.F3J_QueryRow.log
#print axioms AspisR1.F3J_QueryRow.length
#print axioms AspisR1.F3J_QuerySelection.selected
#print axioms AspisR1.F3J_QuerySource.first_pair
#print axioms AspisR1.F3J_RecordPayload.row_bytes
#print axioms AspisR1.F3J_ReseedSampler.payload
#print axioms AspisR1.F3J_ReseedSource.address
#print axioms AspisR1.F3J_ReseedSource.reached
#print axioms AspisR1.F3J_RowBindings.empty
#print axioms AspisR1.F3J_RowBindings.first
#print axioms AspisR1.F3J_RowBindings.payload
#print axioms AspisR1.F3J_RowBindings.bound
#print axioms AspisR1.F3J_RunState.of_run
#print axioms AspisR1.F3J_SamplerCompose.logs
#print axioms AspisR1.F3J_SamplerCompose.value
#print axioms AspisR1.F3J_SamplerRun.length
#print axioms AspisR1.F3J_SamplerRun.split
#print axioms AspisR1.F3J_SamplerStep.step
#print axioms AspisR1.F3J_SamplerStructure.statement
#print axioms AspisR1.F3J_SamplerStructure.pair
#print axioms AspisR1.F3J_ScalarCode.scalar
#print axioms AspisR1.F3J_ScalarCode.rho
#print axioms AspisR1.F3J_SemanticLog.consistent
#print axioms AspisR1.F3J_SemanticLog.payload
#print axioms AspisR1.F3J_SemanticPrefix.positive
#print axioms AspisR1.F3J_SemanticValue.payload
#print axioms AspisR1.F3J_SourceBlock.sample
#print axioms AspisR1.F3J_SourceBlockValue.returned
#print axioms AspisR1.F3J_ValidatedLog.semantic

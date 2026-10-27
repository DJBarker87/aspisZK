import F3L_AccumulatorExt
import F3L_AlignedPrefix
import F3L_CheckpointNumeric
import F3L_ClosedGamma
import F3L_ClosedOrdinary
import F3L_EraseIndex
import F3L_FieldsTransport
import F3L_GammaChallenge
import F3L_GammaEntry
import F3L_GammaMeaning
import F3L_InputDiscovery
import F3L_InputOpening
import F3L_LateFieldEquality
import F3L_LateFields
import F3L_MatchingChallenges
import F3L_MatchingFromEntries
import F3L_ModelRead
import F3L_NativeDiscovery33
import F3L_NativeFields33
import F3L_NativePort33
import F3L_NativePreparedModel
import F3L_OpeningAlphaValues
import F3L_OpeningDataFields
import F3L_OpeningFields
import F3L_OpeningInputLate
import F3L_OpeningLateEntries
import F3L_OpeningPairValues
import F3L_OrdinaryChallenge
import F3L_OrdinaryEntry
import F3L_OrdinaryMeaning
import F3L_OrdinaryReads
import F3L_ParsedSampler
import F3L_PreparePort
import F3L_PreparedDiscovery
import F3L_PreparedExt
import F3L_PreparedInputFields
import F3L_PreparedModel
import F3L_PreparedModelSix
import F3L_PreparedPort
import F3L_PreparedQueryPort
import F3L_PreparedRemaining
import F3L_PreparedRoots
import F3L_RestoreChallenge
import F3L_RhoCanonical
import F3L_RhoChallenge
import F3L_RhoEntry
import F3L_RhoMeaning
import F3L_SamplerAligned
import F3L_SamplerAt
import F3L_SamplerMessages
import F3L_SamplerOrdinary
import F3L_SamplerStatement
import F3L_SamplingSlots
import F3L_SemanticInventory
import F3L_SourceAlphaIndex
import F3L_SourceAlphaValues
import F3L_SourceNumeric
import F3L_SourcePrepared
import F3L_TypedFields
import F3L_WriterAccumulator
import F3L_WriterAlpha
import F3L_WriterBody
import F3L_WriterCoordinates
import F3L_WriterNumeric
import F3L_WriterPreparedEq
import F3L_WriterPreparedScalar
import F3L_WriterRemaining
import F3L_WriterSemanticAlpha
import F3L_WriterSourceScalar

set_option autoImplicit false

#print axioms AspisR1.F3L_AccumulatorExt.fields
#print axioms AspisR1.F3L_AlignedPrefix.aligned
#print axioms AspisR1.F3L_CheckpointNumeric.stage
#print axioms AspisR1.F3L_ClosedGamma.value
#print axioms AspisR1.F3L_ClosedOrdinary.value
#print axioms AspisR1.F3L_EraseIndex.entry
#print axioms AspisR1.F3L_FieldsTransport.fields
#print axioms AspisR1.F3L_GammaChallenge.value
#print axioms AspisR1.F3L_GammaEntry.entry
#print axioms AspisR1.F3L_GammaMeaning.value
#print axioms AspisR1.F3L_InputDiscovery.exists_input
#print axioms AspisR1.F3L_InputOpening.exists_view
#print axioms AspisR1.F3L_LateFieldEquality.rho_state
#print axioms AspisR1.F3L_LateFields.exists_fields
#print axioms AspisR1.F3L_MatchingChallenges.fields
#print axioms AspisR1.F3L_MatchingFromEntries.fields
#print axioms AspisR1.F3L_ModelRead.read
#print axioms AspisR1.F3L_NativeDiscovery33.native
#print axioms AspisR1.F3L_NativeFields33.native
#print axioms AspisR1.F3L_NativePort33.native
#print axioms AspisR1.F3L_NativePreparedModel.native
#print axioms AspisR1.F3L_OpeningAlphaValues.entries
#print axioms AspisR1.F3L_OpeningDataFields.fields
#print axioms AspisR1.F3L_OpeningFields.fields
#print axioms AspisR1.F3L_OpeningInputLate.fields
#print axioms AspisR1.F3L_OpeningLateEntries.entries
#print axioms AspisR1.F3L_OpeningPairValues.entries
#print axioms AspisR1.F3L_OrdinaryChallenge.value
#print axioms AspisR1.F3L_OrdinaryEntry.entry
#print axioms AspisR1.F3L_OrdinaryMeaning.value
#print axioms AspisR1.F3L_OrdinaryReads.read
#print axioms AspisR1.F3L_ParsedSampler.parsed
#print axioms AspisR1.F3L_PreparePort.port
#print axioms AspisR1.F3L_PreparedDiscovery.from_cut
#print axioms AspisR1.F3L_PreparedExt.fields
#print axioms AspisR1.F3L_PreparedInputFields.from_cut
#print axioms AspisR1.F3L_PreparedModel.from_cut
#print axioms AspisR1.F3L_PreparedModelSix.fields
#print axioms AspisR1.F3L_PreparedPort.from_cut
#print axioms AspisR1.F3L_PreparedQueryPort.queries
#print axioms AspisR1.F3L_PreparedRemaining.remaining
#print axioms AspisR1.F3L_PreparedRoots.roots
#print axioms AspisR1.F3L_RestoreChallenge.ordinary
#print axioms AspisR1.F3L_RhoCanonical.sample
#print axioms AspisR1.F3L_RhoCanonical.scalar
#print axioms AspisR1.F3L_RhoChallenge.value
#print axioms AspisR1.F3L_RhoEntry.entry
#print axioms AspisR1.F3L_RhoMeaning.value
#print axioms AspisR1.F3L_SamplerAligned.aligned
#print axioms AspisR1.F3L_SamplerAt.entry
#print axioms AspisR1.F3L_SamplerMessages.entry
#print axioms AspisR1.F3L_SamplerOrdinary.initial
#print axioms AspisR1.F3L_SamplerOrdinary.payload
#print axioms AspisR1.F3L_SamplerStatement.statement
#print axioms AspisR1.F3L_SamplingSlots.ordinary
#print axioms AspisR1.F3L_SamplingSlots.gamma
#print axioms AspisR1.F3L_SemanticInventory.remaining_source
#print axioms AspisR1.F3L_SourceAlphaIndex.alpha1
#print axioms AspisR1.F3L_SourceAlphaValues.alpha
#print axioms AspisR1.F3L_SourceNumeric.wide
#print axioms AspisR1.F3L_SourceNumeric.qm
#print axioms AspisR1.F3L_TypedFields.fields
#print axioms AspisR1.F3L_WriterAccumulator.numeric
#print axioms AspisR1.F3L_WriterAlpha.alpha
#print axioms AspisR1.F3L_WriterBody.body
#print axioms AspisR1.F3L_WriterCoordinates.coordinates
#print axioms AspisR1.F3L_WriterNumeric.exact_k
#print axioms AspisR1.F3L_WriterNumeric.exact_e
#print axioms AspisR1.F3L_WriterPreparedEq.numeric
#print axioms AspisR1.F3L_WriterPreparedScalar.fields
#print axioms AspisR1.F3L_WriterRemaining.fields
#print axioms AspisR1.F3L_WriterSemanticAlpha.semantic_alpha
#print axioms AspisR1.F3L_WriterSourceScalar.exact_e
#print axioms AspisR1.F3L_WriterSourceScalar.exact_k

#print AspisR1.F3L_NativePreparedModel.native
#print AspisR1.F3L_PreparedRemaining.remaining
#print AspisR1.F3L_CheckpointNumeric.stage

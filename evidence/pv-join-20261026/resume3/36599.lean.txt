import R1Z.PV_Join_CombinedAuditPart1
import R1Z.PV_Join_CombinedAuditPart2
import R1Z.PV_Join_CombinedAuditPart3
import R1Z.PV_Join_CombinedAuditPart4
import R1Z.PV_Join_CombinedAuditPart5
import R1Z.PV_Join_CombinedAuditPart6
import R1Z.PrivacyR1HeadlineDeployedReal
import R1Z.PV_Join_AggregateCaller
import R1Z.PV_Join_AuditProjection
import R1Z.PV_Join_Borrow
import R1Z.PV_Join_BorrowCaller
import R1Z.PV_Join_BorrowDictionary
import R1Z.PV_Join_CB3
import R1Z.PV_Join_CB3Boundary
import R1Z.PV_Join_CB3Flat
import R1Z.PV_Join_ClosureCheckpoint
import R1Z.PV_Join_CodecCaller
import R1Z.PV_Join_CodecDictionary
import R1Z.PV_Join_Codecs
import R1Z.PV_Join_Current100
import R1Z.PV_Join_Current101
import R1Z.PV_Join_Current105
import R1Z.PV_Join_Current71
import R1Z.PV_Join_Current72
import R1Z.PV_Join_Current80
import R1Z.PV_Join_DictInspect
import R1Z.PV_Join_Embedding
import R1Z.PV_Join_EmbeddingWord
import R1Z.PV_Join_Field
import R1Z.PV_Join_FieldCaller
import R1Z.PV_Join_FieldDictionary
import R1Z.PV_Join_FinalAudit
import R1Z.PV_Join_FixtureData
import R1Z.PV_Join_FixtureInputs
import R1Z.PV_Join_FixtureSelected
import R1Z.PV_Join_Generic
import R1Z.PV_Join_Heap
import R1Z.PV_Join_HeapCompatibility
import R1Z.PV_Join_Inspect
import R1Z.PV_Join_InvLoop
import R1Z.PV_Join_InvSource
import R1Z.PV_Join_LedgerSource
import R1Z.PV_Join_Merkle
import R1Z.PV_Join_NativeAudit
import R1Z.PV_Join_NativeNeg101
import R1Z.PV_Join_NativeOp20Carrier
import R1Z.PV_Join_NegTransport
import R1Z.PV_Join_Op20Value
import R1Z.PV_Join_ParserTransport
import R1Z.PV_Join_ProofClosure
import R1Z.PV_Join_PublicCaller
import R1Z.PV_Join_PublicCarrierBridge
import R1Z.PV_Join_PublicDataIff
import R1Z.PV_Join_PublicDictionary
import R1Z.PV_Join_PublicInstall
import R1Z.PV_Join_PublicOp20
import R1Z.PV_Join_RawSelectedMismatch
import R1Z.PV_Join_State
import R1Z.PV_Join_StateChanged
import R1Z.PV_Join_StoreLedgerSource

-- All public theorem declarations in the PV_Join modules, including inherited drafts.
#print axioms R1Z.PV_Join_AggregateCaller.dictionary
#print axioms R1Z.PV_Join_AggregateCaller.refinement_of_data
#print axioms R1Z.PV_Join_AuditProjection.native_attempt_good
#print axioms R1Z.PV_Join_AuditProjection.public_body_good
#print axioms R1Z.PV_Join_AuditProjection.whole_of_bytes
#print axioms R1Z.PV_Join_Borrow.op127_source
#print axioms R1Z.PV_Join_Borrow.op128_source
#print axioms R1Z.PV_Join_Borrow.op130_source
#print axioms R1Z.PV_Join_Borrow.op131_source
#print axioms R1Z.PV_Join_BorrowCaller.refinement_of_data
#print axioms R1Z.PV_Join_BorrowDictionary.dictionary
#print axioms R1Z.PV_Join_CB3.op225_source
#print axioms R1Z.PV_Join_CB3.op246_source
#print axioms R1Z.PV_Join_CB3Boundary.body
#print axioms R1Z.PV_Join_CB3Boundary.op120_source
#print axioms R1Z.PV_Join_CB3Boundary.reduce
#print axioms R1Z.PV_Join_CB3Boundary.selected_bridge
#print axioms R1Z.PV_Join_CB3Boundary.step
#print axioms R1Z.PV_Join_CB3Flat.op51_source
#print axioms R1Z.PV_Join_CB3Flat.selected_bridge
#print axioms R1Z.PV_Join_CodecCaller.refinement_of_data
#print axioms R1Z.PV_Join_CodecDictionary.dictionary
#print axioms R1Z.PV_Join_Codecs.op71_source
#print axioms R1Z.PV_Join_Codecs.op72_source
#print axioms R1Z.PV_Join_Codecs.op80_source
#print axioms R1Z.PV_Join_Current100.complex
#print axioms R1Z.PV_Join_Current100.op100_source
#print axioms R1Z.PV_Join_Current100.quartic
#print axioms R1Z.PV_Join_Current100.scalar
#print axioms R1Z.PV_Join_Current100.selected_bridge
#print axioms R1Z.PV_Join_Current100.wide
#print axioms R1Z.PV_Join_Current101.complex
#print axioms R1Z.PV_Join_Current101.op101_source
#print axioms R1Z.PV_Join_Current101.quartic
#print axioms R1Z.PV_Join_Current101.scalar
#print axioms R1Z.PV_Join_Current101.selected_bridge
#print axioms R1Z.PV_Join_Current105.op105_source
#print axioms R1Z.PV_Join_Current105.selected_bridge
#print axioms R1Z.PV_Join_Current71.complex
#print axioms R1Z.PV_Join_Current71.op71_source
#print axioms R1Z.PV_Join_Current71.quartic
#print axioms R1Z.PV_Join_Current71.scalar
#print axioms R1Z.PV_Join_Current71.selected_bridge
#print axioms R1Z.PV_Join_Current72.op72_source
#print axioms R1Z.PV_Join_Current80.op80_source
#print axioms R1Z.PV_Join_Embedding.body
#print axioms R1Z.PV_Join_Embedding.op110_source
#print axioms R1Z.PV_Join_Embedding.quartic
#print axioms R1Z.PV_Join_Embedding.selected_bridge
#print axioms R1Z.PV_Join_EmbeddingWord.canonical
#print axioms R1Z.PV_Join_EmbeddingWord.construct
#print axioms R1Z.PV_Join_EmbeddingWord.reduce
#print axioms R1Z.PV_Join_Field.op100_source
#print axioms R1Z.PV_Join_Field.op101_source
#print axioms R1Z.PV_Join_Field.op105_source
#print axioms R1Z.PV_Join_Field.op107_source
#print axioms R1Z.PV_Join_Field.op109_source
#print axioms R1Z.PV_Join_FieldCaller.refinement_of_data
#print axioms R1Z.PV_Join_FieldDictionary.dictionary
#print axioms R1Z.PV_Join_FixtureData.criterion
#print axioms R1Z.PV_Join_FixtureInputs.body_source
#print axioms R1Z.PV_Join_FixtureInputs.same_record
#print axioms R1Z.PV_Join_FixtureInputs.semantic_columns
#print axioms R1Z.PV_Join_FixtureSelected.both_source
#print axioms R1Z.PV_Join_Generic.op3_source
#print axioms R1Z.PV_Join_Generic.op77_source
#print axioms R1Z.PV_Join_Heap.op81_source
#print axioms R1Z.PV_Join_HeapCompatibility.dictionary
#print axioms R1Z.PV_Join_HeapCompatibility.filled_congr
#print axioms R1Z.PV_Join_HeapCompatibility.mapError
#print axioms R1Z.PV_Join_HeapCompatibility.reserve
#print axioms R1Z.PV_Join_InvLoop.body
#print axioms R1Z.PV_Join_InvLoop.mul
#print axioms R1Z.PV_Join_InvLoop.pow
#print axioms R1Z.PV_Join_InvLoop.run
#print axioms R1Z.PV_Join_InvSource.inverse
#print axioms R1Z.PV_Join_LedgerSource.body_source
#print axioms R1Z.PV_Join_Merkle.op82_source
#print axioms R1Z.PV_Join_Merkle.op83_source
#print axioms R1Z.PV_Join_Merkle.op84_source
#print axioms R1Z.PV_Join_Merkle.op86_source
#print axioms R1Z.PV_Join_NativeAudit.data_of_model_bytes
#print axioms R1Z.PV_Join_NativeAudit.native_attempt_good
#print axioms R1Z.PV_Join_NativeNeg101.complex
#print axioms R1Z.PV_Join_NativeNeg101.quartic
#print axioms R1Z.PV_Join_NativeNeg101.scalar
#print axioms R1Z.PV_Join_NegTransport.complex100
#print axioms R1Z.PV_Join_NegTransport.complex101
#print axioms R1Z.PV_Join_NegTransport.mask_false
#print axioms R1Z.PV_Join_NegTransport.mask_true
#print axioms R1Z.PV_Join_NegTransport.quartic100
#print axioms R1Z.PV_Join_NegTransport.quartic101
#print axioms R1Z.PV_Join_NegTransport.scalar100
#print axioms R1Z.PV_Join_NegTransport.scalar101
#print axioms R1Z.PV_Join_NegTransport.sub
#print axioms R1Z.PV_Join_NegTransport.wide100
#print axioms R1Z.PV_Join_Op20Value.cb3_roundtrip
#print axioms R1Z.PV_Join_Op20Value.components
#print axioms R1Z.PV_Join_Op20Value.native_roundtrip
#print axioms R1Z.PV_Join_ParserTransport.bind_congr
#print axioms R1Z.PV_Join_ParserTransport.complex
#print axioms R1Z.PV_Join_ParserTransport.quartic
#print axioms R1Z.PV_Join_ParserTransport.scalar
#print axioms R1Z.PV_Join_PublicCaller.caller_callback_removed
#print axioms R1Z.PV_Join_PublicCaller.refinement_of_data
#print axioms R1Z.PV_Join_PublicCarrierBridge.roundtrip
#print axioms R1Z.PV_Join_PublicCarrierBridge.source
#print axioms R1Z.PV_Join_PublicCarrierBridge.source_roundtrip
#print axioms R1Z.PV_Join_PublicDataIff.criterion
#print axioms R1Z.PV_Join_PublicDataIff.refinement_of_bytes
#print axioms R1Z.PV_Join_PublicDictionary.dictionary
#print axioms R1Z.PV_Join_PublicDictionary.raw_form
#print axioms R1Z.PV_Join_PublicInstall.callback_removed
#print axioms R1Z.PV_Join_PublicInstall.p6_source
#print axioms R1Z.PV_Join_PublicInstall.source
#print axioms R1Z.PV_Join_PublicOp20.cb3_roundtrip
#print axioms R1Z.PV_Join_PublicOp20.native_roundtrip
#print axioms R1Z.PV_Join_PublicOp20.selected_source
#print axioms R1Z.PV_Join_RawSelectedMismatch.no_universal_raw_source
#print axioms R1Z.PV_Join_RawSelectedMismatch.raw_entry_unconstrained
#print axioms R1Z.PV_Join_State.op111_source
#print axioms R1Z.PV_Join_State.op118_source
#print axioms R1Z.PV_Join_StateChanged.op114_source
#print axioms R1Z.PV_Join_StateChanged.selected_bridge
#print axioms R1Z.PV_Join_StateChanged.source_status
#print axioms R1Z.PV_Join_StoreLedgerSource.body_source
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed

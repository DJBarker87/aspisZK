import PV_L2B_Cursor
import PV_L2B_EntropyTrace
import PV_L2B_Guards
import PV_L2B_JointTransport
import PV_L2B_Rejection
import PV_L2B_SamplerLaw
import PV_L2B_SourceWords
import R1Z.PV_CB3_CallbackBundle
import R1Z.PV_CBL_CallbackBundle
import R1Z.PV_CBL_CallbackPublication
import R1Z.PV_CBM_CallbackBundle
import R1Z.PV_CB_ArrayTransport
import R1Z.PV_CB_CandidateCodecs
import R1Z.PV_CB_CandidateCore
import R1Z.PV_CB_CandidateDictionary
import R1Z.PV_CB_CandidateField
import R1Z.PV_CB_CandidatePublic
import R1Z.PV_CB_CandidateZeroizing
import R1Z.PV_CB_CanonicalArrays
import R1Z.PV_CB_CanonicalComplex
import R1Z.PV_CB_CanonicalConstants
import R1Z.PV_CB_CanonicalFill
import R1Z.PV_CB_CanonicalForward
import R1Z.PV_CB_CanonicalHorner
import R1Z.PV_CB_CanonicalLinears
import R1Z.PV_CB_CanonicalLinearsLoop
import R1Z.PV_CB_CanonicalM31
import R1Z.PV_CB_CanonicalM31Ops
import R1Z.PV_CB_CanonicalMaskBasis
import R1Z.PV_CB_CanonicalMaskCell
import R1Z.PV_CB_CanonicalMaskRoot
import R1Z.PV_CB_CanonicalNeg
import R1Z.PV_CB_CanonicalPower26
import R1Z.PV_CB_CanonicalPreparedCtor
import R1Z.PV_CB_CanonicalPreparedMul
import R1Z.PV_CB_CanonicalPreparedPart
import R1Z.PV_CB_CanonicalQuartic
import R1Z.PV_CB_CanonicalQuarticMore
import R1Z.PV_CB_CanonicalSampler
import R1Z.PV_CB_CanonicalTower
import R1Z.PV_CB_CanonicalUpdate
import R1Z.PV_CB_CompressCanonical
import R1Z.PV_CB_CompressCanonicalArray16
import R1Z.PV_CB_CompressCanonicalContext
import R1Z.PV_CB_CompressCanonicalFinite
import R1Z.PV_CB_CompressCanonicalRead
import R1Z.PV_CB_CompressConstructors
import R1Z.PV_CB_CompressSelectedCanonical
import R1Z.PV_CB_CompressSelectedEntries
import R1Z.PV_CB_CompressSupport
import R1Z.PV_CB_CurrentComplex
import R1Z.PV_CB_CurrentComplexMore
import R1Z.PV_CB_CurrentNeg
import R1Z.PV_CB_CurrentQuartic
import R1Z.PV_CB_CurrentTotal
import R1Z.PV_CB_EncoderTotal
import R1Z.PV_CB_FillCellEq
import R1Z.PV_CB_FillLoopsEq
import R1Z.PV_CB_FillStepsEq
import R1Z.PV_CB_FiniteStepEq
import R1Z.PV_CB_ForestProducedReference
import R1Z.PV_CB_ForestProducedValues
import R1Z.PV_CB_ForestProducerBody
import R1Z.PV_CB_ForestProducerCarrier
import R1Z.PV_CB_ForestProducerContract
import R1Z.PV_CB_ForestProducerLoop
import R1Z.PV_CB_ForestProducerMetadata
import R1Z.PV_CB_ForestProducerRoot
import R1Z.PV_CB_ForestProducerTotal
import R1Z.PV_CB_ForestSampledCallsite
import R1Z.PV_CB_ForwardLoop
import R1Z.PV_CB_ForwardRange
import R1Z.PV_CB_HornerBody
import R1Z.PV_CB_HornerCanonicalCell
import R1Z.PV_CB_HornerCanonicalIndexed
import R1Z.PV_CB_HornerCell
import R1Z.PV_CB_HornerCoefficientPrefix
import R1Z.PV_CB_HornerFiniteCells
import R1Z.PV_CB_HornerFiniteTransport
import R1Z.PV_CB_HornerPrefixControl
import R1Z.PV_CB_HornerReach
import R1Z.PV_CB_HornerScalarTransport
import R1Z.PV_CB_Independent
import R1Z.PV_CB_MaskCell
import R1Z.PV_CB_MaskExponentTables
import R1Z.PV_CB_MaskFillBody
import R1Z.PV_CB_MaskFillLoop
import R1Z.PV_CB_MaskHorner
import R1Z.PV_CB_MaskIndices
import R1Z.PV_CB_MaskLeaves
import R1Z.PV_CB_MaskLinearsFinite
import R1Z.PV_CB_MaskRootEq
import R1Z.PV_CB_MaskSource
import R1Z.PV_CB_Op100Exact
import R1Z.PV_CB_Op101Exact
import R1Z.PV_CB_Op105Exact
import R1Z.PV_CB_Op107Exact
import R1Z.PV_CB_Op107Transport
import R1Z.PV_CB_Op109CanonicalBinding
import R1Z.PV_CB_Op109Exact
import R1Z.PV_CB_Op109RefTransport
import R1Z.PV_CB_Op109Transport
import R1Z.PV_CB_Op110Source
import R1Z.PV_CB_Op111Source
import R1Z.PV_CB_Op114Source
import R1Z.PV_CB_Op118Exact
import R1Z.PV_CB_Op118Transport
import R1Z.PV_CB_Op127Source
import R1Z.PV_CB_Op128Source
import R1Z.PV_CB_Op130Source
import R1Z.PV_CB_Op131Source
import R1Z.PV_CB_Op223Boundary
import R1Z.PV_CB_Op223Callsite
import R1Z.PV_CB_Op223CanonicalCallsite
import R1Z.PV_CB_Op223CanonicalDomain
import R1Z.PV_CB_Op223CellSupport
import R1Z.PV_CB_Op223Domain
import R1Z.PV_CB_Op223ForestCallsite
import R1Z.PV_CB_Op223ForestLocalCallsite
import R1Z.PV_CB_Op223LaneAgreement
import R1Z.PV_CB_Op223LimbSupport
import R1Z.PV_CB_Op223LocalCanonicalCallsite
import R1Z.PV_CB_Op223ProducedCallsite
import R1Z.PV_CB_Op223TagCanonical
import R1Z.PV_CB_Op223TupleSupport
import R1Z.PV_CB_Op229Source
import R1Z.PV_CB_Op71Exact
import R1Z.PV_CB_Op72Exact
import R1Z.PV_CB_Op77Source
import R1Z.PV_CB_Op80Exact
import R1Z.PV_CB_Op82Source
import R1Z.PV_CB_Op83Source
import R1Z.PV_CB_Op84Exact
import R1Z.PV_CB_Op86Source
import R1Z.PV_CB_OptionDiscriminant
import R1Z.PV_CB_OwnedMaskFill
import R1Z.PV_CB_OwnedMaskHorner
import R1Z.PV_CB_OwnedMaskHornerEq
import R1Z.PV_CB_OwnedMaskLeaves
import R1Z.PV_CB_OwnedMaskLinears
import R1Z.PV_CB_OwnedMaskLinearsEq
import R1Z.PV_CB_OwnedMaskTotal
import R1Z.PV_CB_PartialArrayUpdate
import R1Z.PV_CB_PartialForward
import R1Z.PV_CB_PreparedTotal
import R1Z.PV_CB_ProducerBind
import R1Z.PV_CB_ProducerCallsite
import R1Z.PV_CB_ProducerCell
import R1Z.PV_CB_ProducerContext
import R1Z.PV_CB_ProducerLimb
import R1Z.PV_CB_ProducerLocalCallsite
import R1Z.PV_CB_ProducerLocalCell
import R1Z.PV_CB_ProducerLocalLimb
import R1Z.PV_CB_ProducerLocalSelected
import R1Z.PV_CB_ProducerLocalTuple
import R1Z.PV_CB_ProducerMake16
import R1Z.PV_CB_ProducerMetadataCarrier
import R1Z.PV_CB_ProducerOffsetChoice
import R1Z.PV_CB_ProducerOffsetControl
import R1Z.PV_CB_ProducerOffsets
import R1Z.PV_CB_ProducerPost
import R1Z.PV_CB_ProducerRead
import R1Z.PV_CB_ProducerReadRestriction
import R1Z.PV_CB_ProducerReference
import R1Z.PV_CB_ProducerSelected
import R1Z.PV_CB_ProducerTraceData
import R1Z.PV_CB_ProducerTry
import R1Z.PV_CB_ProducerTuple
import R1Z.PV_CB_QuarticProjections
import R1Z.PV_CB_ReachBind
import R1Z.PV_CB_ReverseWrap
import R1Z.PV_CB_TakeSource
import R1Z.PV_CB_TowerLaneJoin
import R1Z.PV_CB_TupleProducerBody
import R1Z.PV_CB_TupleProducerCarrier
import R1Z.PV_CB_TupleProducerContract
import R1Z.PV_CB_TupleProducerInvariant
import R1Z.PV_CB_TupleProducerLoop
import R1Z.PV_CB_TupleProducerMetadata
import R1Z.PV_CB_TupleProducerMetadataLoop
import R1Z.PV_CB_TupleProducerMetadataRoot
import R1Z.PV_CB_TupleProducerOffset
import R1Z.PV_CB_TupleProducerRoot
import R1Z.PV_CB_TupleProducerRootTotal
import R1Z.PV_CB_TupleProducerRow
import R1Z.PV_CB_TupleProducerScalar
import R1Z.PV_CB_TupleProducerSelectors
import R1Z.PV_CB_TupleProducerStep
import R1Z.PV_CB_TupleProducerTotal
import R1Z.PV_Join_AggregateCaller
import R1Z.PV_Op134_ReferenceBundle
import R1Z.PV_Op223_Agreement_CM31_ZERO
import R1Z.PV_Op223_Agreement_CM31_add
import R1Z.PV_Op223_Agreement_CM31_from_m31
import R1Z.PV_Op223_Agreement_CM31_mul
import R1Z.PV_Op223_Agreement_CM31_mul_m31
import R1Z.PV_Op223_Agreement_CM31_sub
import R1Z.PV_Op223_Agreement_M31_ZERO
import R1Z.PV_Op223_Agreement_M31_add
import R1Z.PV_Op223_Agreement_M31_double
import R1Z.PV_Op223_Agreement_M31_mul
import R1Z.PV_Op223_Agreement_M31_reduce_u64
import R1Z.PV_Op223_Agreement_M31_sub
import R1Z.PV_Op223_Agreement_P
import R1Z.PV_Op223_Agreement_QM31_add
import R1Z.PV_Op223_Agreement_QM31_from_cm31
import R1Z.PV_Op223_Agreement_QM31_mul
import R1Z.PV_Op223_Agreement_QM31_mul_m31
import R1Z.PV_Op223_Agreement_ct_add
import R1Z.PV_Op223_Agreement_ct_reduce64
import R1Z.PV_Op223_Agreement_ct_sub
import R1Z.PV_Op223_Agreement_ct_subtract_p
import R1Z.PV_Op223_Agreement_mul_by_r
import R1Z.PV_Op223_Agreement_reduce_u64
import R1Z.PV_Op223_FieldBridge_CM31_mul_m31
import R1Z.PV_Op223_FieldBridge_QM31_add
import R1Z.PV_Op223_FieldBridge_QM31_from_cm31
import R1Z.PV_Op223_FieldBridge_QM31_mul
import R1Z.PV_Op223_FieldBridge_QM31_mul_m31
import R1Z.PV_Op223_FieldBridge_mul_by_r
import R1Z.PV_Op223_SelectedFields
import R1Z.PV_Op223_Source
import R1Z.PV_Op223_V164

-- Combined integration publication audit; no new theorem or source refinement.
#print axioms PV_L2B_Cursor.absolute_decomposition
#print axioms PV_L2B_Cursor.accepted_no_rejection_next
#print axioms PV_L2B_Cursor.block_step
#print axioms PV_L2B_Cursor.cap_cursor_independent
#print axioms PV_L2B_Cursor.cursor_append
#print axioms PV_L2B_Cursor.cursor_cons
#print axioms PV_L2B_Cursor.cursor_nil
#print axioms PV_L2B_Cursor.cursor_rejection_sum
#print axioms PV_L2B_Cursor.first_limb_offset
#print axioms PV_L2B_Cursor.last_byte_bound
#print axioms PV_L2B_Cursor.offset_bound
#print axioms PV_L2B_Cursor.offset_period
#print axioms PV_L2B_Cursor.offset_zero
#print axioms PV_L2B_Cursor.one_rejection_next
#print axioms PV_L2B_Cursor.qm31_consumption_bound
#print axioms PV_L2B_Cursor.qm31_cursor
#print axioms PV_L2B_Cursor.read_word_bound
#print axioms PV_L2B_Cursor.read_word_positive
#print axioms PV_L2B_Cursor.refill_iff
#print axioms PV_L2B_Cursor.word_period
#print axioms PV_L2B_EntropyTrace.accepted_pair
#print axioms PV_L2B_EntropyTrace.branches_relabel
#print axioms PV_L2B_EntropyTrace.conditional_class_total
#print axioms PV_L2B_EntropyTrace.entropy_q_valid
#print axioms PV_L2B_EntropyTrace.first_reject_conditional
#print axioms PV_L2B_EntropyTrace.first_skips_second
#print axioms PV_L2B_EntropyTrace.first_zero
#print axioms PV_L2B_EntropyTrace.full_comparison_count_relabel
#print axioms PV_L2B_EntropyTrace.kind_relabel
#print axioms PV_L2B_EntropyTrace.second_checks_both
#print axioms PV_L2B_EntropyTrace.second_reject_conditional
#print axioms PV_L2B_EntropyTrace.second_zero
#print axioms PV_L2B_EntropyTrace.success_checks_both
#print axioms PV_L2B_Guards.active_zero_guard
#print axioms PV_L2B_Guards.audit_shortcircuit
#print axioms PV_L2B_Guards.balanced_dependent
#print axioms PV_L2B_Guards.balanced_dependent_first
#print axioms PV_L2B_Guards.c1_count_guard
#print axioms PV_L2B_Guards.canonical_guard
#print axioms PV_L2B_Guards.equality_guard
#print axioms PV_L2B_Guards.failed_trace
#print axioms PV_L2B_Guards.helper_option_guard
#print axioms PV_L2B_Guards.inactive_balance
#print axioms PV_L2B_Guards.mask_count_guard
#print axioms PV_L2B_Guards.modular_canonical
#print axioms PV_L2B_Guards.padding_preserves_sum
#print axioms PV_L2B_Guards.padding_total
#print axioms PV_L2B_Guards.paired_helper_cancels
#print axioms PV_L2B_Guards.passing_trace
#print axioms PV_L2B_Guards.sumcheck_boundary
#print axioms PV_L2B_Guards.sumcheck_terminal
#print axioms PV_L2B_Guards.zero_guard
#print axioms PV_L2B_Guards.zmod_canonical
#print axioms PV_L2B_JointTransport.accepted_conditional_uniform
#print axioms PV_L2B_JointTransport.constant_guard_joint
#print axioms PV_L2B_JointTransport.outside_existing_event
#print axioms PV_L2B_JointTransport.rejection_cursor_joint
#print axioms PV_L2B_JointTransport.weighted_joint_transport
#print axioms PV_L2B_Rejection.accept_in_range
#print axioms PV_L2B_Rejection.accepted
#print axioms PV_L2B_Rejection.cap_zero
#print axioms PV_L2B_Rejection.coins_only
#print axioms PV_L2B_Rejection.consumed_le_cap
#print axioms PV_L2B_Rejection.consumed_le_length
#print axioms PV_L2B_Rejection.count_map
#print axioms PV_L2B_Rejection.empty
#print axioms PV_L2B_Rejection.exhausted
#print axioms PV_L2B_Rejection.first_accept
#print axioms PV_L2B_Rejection.reject_at_boundary
#print axioms PV_L2B_Rejection.rejected
#print axioms PV_L2B_Rejection.rejected_prefix
#print axioms PV_L2B_Rejection.same_flags
#print axioms PV_L2B_Rejection.scan_map
#print axioms PV_L2B_Rejection.status_map
#print axioms PV_L2B_Rejection.trace_relabel
#print axioms PV_L2B_SamplerLaw.entropy_accept_partition
#print axioms PV_L2B_SamplerLaw.entropy_pair_normalization
#print axioms PV_L2B_SamplerLaw.entropy_prefix_pair
#print axioms PV_L2B_SamplerLaw.entropy_reject_partition
#print axioms PV_L2B_SamplerLaw.entropy_uniform_pair
#print axioms PV_L2B_SamplerLaw.exhaustion_nonnegative
#print axioms PV_L2B_SamplerLaw.geometric_nonnegative
#print axioms PV_L2B_SamplerLaw.geometric_step
#print axioms PV_L2B_SamplerLaw.geometric_zero
#print axioms PV_L2B_SamplerLaw.prefix_independent
#print axioms PV_L2B_SamplerLaw.prefix_uniform
#print axioms PV_L2B_SamplerLaw.scalar_normalization
#print axioms PV_L2B_SamplerLaw.scalar_prefix_product
#print axioms PV_L2B_SamplerLaw.scalar_trace_law
#print axioms PV_L2B_SamplerLaw.scalar_uniform
#print axioms PV_L2B_SamplerLaw.source_scalar_exhaustion_probability
#print axioms PV_L2B_SamplerLaw.source_scalar_reject_probability
#print axioms PV_L2B_SamplerLaw.success_closed
#print axioms PV_L2B_SamplerLaw.success_zero
#print axioms PV_L2B_SamplerLaw.total_capped
#print axioms PV_L2B_SamplerLaw.uniform_on_success
#print axioms PV_L2B_SamplerLaw.value_factor
#print axioms PV_L2B_SourceWords.source_consumed_bound
#print axioms PV_L2B_SourceWords.source_count_relabel
#print axioms PV_L2B_SourceWords.source_scan
#print axioms R1Z.PV_CB3_CallbackBundle.op120_source
#print axioms R1Z.PV_CB3_CallbackBundle.op225_source
#print axioms R1Z.PV_CB3_CallbackBundle.op229_source
#print axioms R1Z.PV_CB3_CallbackBundle.op246_source
#print axioms R1Z.PV_CB3_CallbackBundle.op51_source
#print axioms R1Z.PV_CBL_CallbackBundle.AppendTypes
#print axioms R1Z.PV_CBL_CallbackBundle.op25_source
#print axioms R1Z.PV_CBL_CallbackBundle.op25_source_append
#print axioms R1Z.PV_CBL_CallbackBundle.op25_source_string
#print axioms R1Z.PV_CBL_CallbackBundle.op26_source
#print axioms R1Z.PV_CBL_CallbackBundle.op28_source
#print axioms R1Z.PV_CBL_CallbackBundle.op28_source_all
#print axioms R1Z.PV_CBL_CallbackBundle.op28_source_append
#print axioms R1Z.PV_CBL_CallbackBundle.op29_source
#print axioms R1Z.PV_CBL_CallbackBundle.op29_source_append
#print axioms R1Z.PV_CBL_CallbackBundle.op29_source_string
#print axioms R1Z.PV_CBL_CallbackBundle.op30_source_append
#print axioms R1Z.PV_CBL_CallbackBundle.op31_source_append
#print axioms R1Z.PV_CBL_CallbackBundle.op34_source
#print axioms R1Z.PV_CBL_CallbackBundle.op34_source_all
#print axioms R1Z.PV_CBL_CallbackBundle.op34_source_append
#print axioms R1Z.PV_CBL_CallbackBundle.op34_source_string
#print axioms R1Z.PV_CBL_CallbackBundle.op35_source
#print axioms R1Z.PV_CBL_CallbackBundle.op35_source_all
#print axioms R1Z.PV_CBL_CallbackBundle.op35_source_append
#print axioms R1Z.PV_CBL_CallbackBundle.op35_source_string
#print axioms R1Z.PV_CBL_CallbackBundle.selectedAppend
#print axioms R1Z.PV_CBL_CallbackBundle.selectedJoin
#print axioms R1Z.PV_CBL_CallbackBundle.soft_compress_source
#print axioms R1Z.PV_CBL_CallbackBundle.soft_digest_source
#print axioms R1Z.PV_CBL_CallbackBundle.soft_finalize_source
#print axioms R1Z.PV_CBL_CallbackBundle.soft_padding_source
#print axioms R1Z.PV_CBL_CallbackBundle.soft_update_source
#print axioms R1Z.PV_CBM_CallbackBundle.op132_reference
#print axioms R1Z.PV_CBM_CallbackBundle.op133_reference
#print axioms R1Z.PV_CBM_CallbackBundle.op134_reference
#print axioms R1Z.PV_CB_ArrayTransport.roundtrip
#print axioms R1Z.PV_CB_CandidateDictionary.op100
#print axioms R1Z.PV_CB_CandidateDictionary.op101
#print axioms R1Z.PV_CB_CandidateDictionary.op105
#print axioms R1Z.PV_CB_CandidateDictionary.op107
#print axioms R1Z.PV_CB_CandidateDictionary.op109
#print axioms R1Z.PV_CB_CandidateDictionary.op110
#print axioms R1Z.PV_CB_CandidateDictionary.op111
#print axioms R1Z.PV_CB_CandidateDictionary.op114
#print axioms R1Z.PV_CB_CandidateDictionary.op118
#print axioms R1Z.PV_CB_CandidateDictionary.op127
#print axioms R1Z.PV_CB_CandidateDictionary.op128
#print axioms R1Z.PV_CB_CandidateDictionary.op130
#print axioms R1Z.PV_CB_CandidateDictionary.op131
#print axioms R1Z.PV_CB_CandidateDictionary.op229
#print axioms R1Z.PV_CB_CandidateDictionary.op3
#print axioms R1Z.PV_CB_CandidateDictionary.op71
#print axioms R1Z.PV_CB_CandidateDictionary.op72
#print axioms R1Z.PV_CB_CandidateDictionary.op77
#print axioms R1Z.PV_CB_CandidateDictionary.op80
#print axioms R1Z.PV_CB_CandidateDictionary.op82
#print axioms R1Z.PV_CB_CandidateDictionary.op83
#print axioms R1Z.PV_CB_CandidateDictionary.op84
#print axioms R1Z.PV_CB_CandidateDictionary.op86
#print axioms R1Z.PV_CB_CanonicalArrays.read
#print axioms R1Z.PV_CB_CanonicalArrays.repeat_valid
#print axioms R1Z.PV_CB_CanonicalComplex.add
#print axioms R1Z.PV_CB_CanonicalComplex.mul
#print axioms R1Z.PV_CB_CanonicalComplex.r
#print axioms R1Z.PV_CB_CanonicalComplex.source
#print axioms R1Z.PV_CB_CanonicalComplex.sub
#print axioms R1Z.PV_CB_CanonicalComplex.valid_current
#print axioms R1Z.PV_CB_CanonicalConstants.one
#print axioms R1Z.PV_CB_CanonicalConstants.zero
#print axioms R1Z.PV_CB_CanonicalFill.c1
#print axioms R1Z.PV_CB_CanonicalFill.mask
#print axioms R1Z.PV_CB_CanonicalFill.owned_c1
#print axioms R1Z.PV_CB_CanonicalFill.owned_mask
#print axioms R1Z.PV_CB_CanonicalForward.finite
#print axioms R1Z.PV_CB_CanonicalHorner.finite
#print axioms R1Z.PV_CB_CanonicalHorner.owned
#print axioms R1Z.PV_CB_CanonicalHorner.source
#print axioms R1Z.PV_CB_CanonicalLinears.source
#print axioms R1Z.PV_CB_CanonicalLinearsLoop.finite
#print axioms R1Z.PV_CB_CanonicalLinearsLoop.source
#print axioms R1Z.PV_CB_CanonicalM31.mul
#print axioms R1Z.PV_CB_CanonicalM31.reduce
#print axioms R1Z.PV_CB_CanonicalM31Ops.add
#print axioms R1Z.PV_CB_CanonicalM31Ops.double
#print axioms R1Z.PV_CB_CanonicalM31Ops.sub
#print axioms R1Z.PV_CB_CanonicalMaskBasis.i
#print axioms R1Z.PV_CB_CanonicalMaskBasis.r
#print axioms R1Z.PV_CB_CanonicalMaskBasis.tower
#print axioms R1Z.PV_CB_CanonicalMaskCell.cell
#print axioms R1Z.PV_CB_CanonicalMaskRoot.owned
#print axioms R1Z.PV_CB_CanonicalMaskRoot.source
#print axioms R1Z.PV_CB_CanonicalNeg.neg
#print axioms R1Z.PV_CB_CanonicalPower26.power26
#print axioms R1Z.PV_CB_CanonicalPreparedCtor.new
#print axioms R1Z.PV_CB_CanonicalPreparedCtor.new_part
#print axioms R1Z.PV_CB_CanonicalPreparedMul.mul
#print axioms R1Z.PV_CB_CanonicalPreparedPart.mul_part
#print axioms R1Z.PV_CB_CanonicalQuartic.add
#print axioms R1Z.PV_CB_CanonicalQuartic.mul
#print axioms R1Z.PV_CB_CanonicalQuarticMore.scale
#print axioms R1Z.PV_CB_CanonicalQuarticMore.square
#print axioms R1Z.PV_CB_CanonicalSampler.installed
#print axioms R1Z.PV_CB_CanonicalSampler.selected
#print axioms R1Z.PV_CB_CanonicalTower.old_roundtrip
#print axioms R1Z.PV_CB_CanonicalTower.roundtrip
#print axioms R1Z.PV_CB_CanonicalTower.source
#print axioms R1Z.PV_CB_CanonicalTower.source_current
#print axioms R1Z.PV_CB_CanonicalTower.valid_current
#print axioms R1Z.PV_CB_CanonicalUpdate.list_set
#print axioms R1Z.PV_CB_CanonicalUpdate.update
#print axioms R1Z.PV_CB_CompressCanonical.of_callbacks
#print axioms R1Z.PV_CB_CompressCanonical.reference
#print axioms R1Z.PV_CB_CompressCanonicalArray16.reference
#print axioms R1Z.PV_CB_CompressCanonicalArray16.slice_valid
#print axioms R1Z.PV_CB_CompressCanonicalContext.constructors61
#print axioms R1Z.PV_CB_CompressCanonicalContext.constructors66
#print axioms R1Z.PV_CB_CompressCanonicalContext.retained
#print axioms R1Z.PV_CB_CompressCanonicalContext.transfer
#print axioms R1Z.PV_CB_CompressCanonicalFinite.finite
#print axioms R1Z.PV_CB_CompressCanonicalRead.read
#print axioms R1Z.PV_CB_CompressConstructors.cm31
#print axioms R1Z.PV_CB_CompressConstructors.cm31_valid
#print axioms R1Z.PV_CB_CompressConstructors.m31
#print axioms R1Z.PV_CB_CompressConstructors.m31_valid
#print axioms R1Z.PV_CB_CompressSelectedCanonical.context
#print axioms R1Z.PV_CB_CompressSelectedCanonical.reference
#print axioms R1Z.PV_CB_CompressSelectedEntries.entry61
#print axioms R1Z.PV_CB_CompressSelectedEntries.entry66
#print axioms R1Z.PV_CB_CompressSelectedEntries.entry67
#print axioms R1Z.PV_CB_CompressSelectedEntries.entry69
#print axioms R1Z.PV_CB_CompressSelectedEntries.entry70
#print axioms R1Z.PV_CB_CompressSupport.congr
#print axioms R1Z.PV_CB_CurrentComplex.add
#print axioms R1Z.PV_CB_CurrentComplex.mul
#print axioms R1Z.PV_CB_CurrentComplex.sub
#print axioms R1Z.PV_CB_CurrentComplexMore.double
#print axioms R1Z.PV_CB_CurrentComplexMore.scale
#print axioms R1Z.PV_CB_CurrentComplexMore.square
#print axioms R1Z.PV_CB_CurrentNeg.mask_false
#print axioms R1Z.PV_CB_CurrentNeg.mask_true
#print axioms R1Z.PV_CB_CurrentNeg.native
#print axioms R1Z.PV_CB_CurrentQuartic.add
#print axioms R1Z.PV_CB_CurrentQuartic.mul
#print axioms R1Z.PV_CB_CurrentQuartic.r
#print axioms R1Z.PV_CB_CurrentQuartic.scale
#print axioms R1Z.PV_CB_CurrentQuartic.square
#print axioms R1Z.PV_CB_CurrentTotal.c_add
#print axioms R1Z.PV_CB_CurrentTotal.c_double
#print axioms R1Z.PV_CB_CurrentTotal.c_mul
#print axioms R1Z.PV_CB_CurrentTotal.c_r
#print axioms R1Z.PV_CB_CurrentTotal.c_scale
#print axioms R1Z.PV_CB_CurrentTotal.c_square
#print axioms R1Z.PV_CB_CurrentTotal.c_sub
#print axioms R1Z.PV_CB_CurrentTotal.m_add
#print axioms R1Z.PV_CB_CurrentTotal.m_double
#print axioms R1Z.PV_CB_CurrentTotal.m_mul
#print axioms R1Z.PV_CB_CurrentTotal.m_sub
#print axioms R1Z.PV_CB_CurrentTotal.q_add
#print axioms R1Z.PV_CB_CurrentTotal.q_mul
#print axioms R1Z.PV_CB_CurrentTotal.q_scale
#print axioms R1Z.PV_CB_CurrentTotal.q_square
#print axioms R1Z.PV_CB_EncoderTotal.total
#print axioms R1Z.PV_CB_FillCellEq.cell
#print axioms R1Z.PV_CB_FillLoopsEq.c1
#print axioms R1Z.PV_CB_FillLoopsEq.mask
#print axioms R1Z.PV_CB_FillStepsEq.c1
#print axioms R1Z.PV_CB_FillStepsEq.mask
#print axioms R1Z.PV_CB_FiniteStepEq.source
#print axioms R1Z.PV_CB_ForestProducedReference.sampled
#print axioms R1Z.PV_CB_ForestProducedValues.canonical
#print axioms R1Z.PV_CB_ForestProducerBody.legacy
#print axioms R1Z.PV_CB_ForestProducerCarrier.produced
#print axioms R1Z.PV_CB_ForestProducerContract.source
#print axioms R1Z.PV_CB_ForestProducerLoop.legacy
#print axioms R1Z.PV_CB_ForestProducerMetadata.row
#print axioms R1Z.PV_CB_ForestProducerMetadata.source
#print axioms R1Z.PV_CB_ForestProducerRoot.legacy
#print axioms R1Z.PV_CB_ForestProducerRoot.source
#print axioms R1Z.PV_CB_ForestProducerTotal.source
#print axioms R1Z.PV_CB_ForestSampledCallsite.endpoint
#print axioms R1Z.PV_CB_ForwardLoop.source
#print axioms R1Z.PV_CB_ForwardRange.advance_val
#print axioms R1Z.PV_CB_ForwardRange.next_done
#print axioms R1Z.PV_CB_ForwardRange.next_step
#print axioms R1Z.PV_CB_HornerBody.step
#print axioms R1Z.PV_CB_HornerCanonicalCell.representative
#print axioms R1Z.PV_CB_HornerCanonicalCell.total
#print axioms R1Z.PV_CB_HornerCanonicalIndexed.cell
#print axioms R1Z.PV_CB_HornerCell.locality
#print axioms R1Z.PV_CB_HornerCell.read
#print axioms R1Z.PV_CB_HornerCell.scalar_representative
#print axioms R1Z.PV_CB_HornerCoefficientPrefix.finite
#print axioms R1Z.PV_CB_HornerFiniteCells.source
#print axioms R1Z.PV_CB_HornerFiniteTransport.congr
#print axioms R1Z.PV_CB_HornerPrefixControl.owned
#print axioms R1Z.PV_CB_HornerPrefixControl.retained
#print axioms R1Z.PV_CB_HornerReach.body_scalar
#print axioms R1Z.PV_CB_HornerReach.index_bound
#print axioms R1Z.PV_CB_HornerScalarTransport.lift
#print axioms R1Z.PV_CB_Independent.array
#print axioms R1Z.PV_CB_Independent.default_vec
#print axioms R1Z.PV_CB_Independent.empty
#print axioms R1Z.PV_CB_Independent.pop
#print axioms R1Z.PV_CB_Independent.take
#print axioms R1Z.PV_CB_MaskCell.c1_total
#print axioms R1Z.PV_CB_MaskCell.mask_total
#print axioms R1Z.PV_CB_MaskCell.total
#print axioms R1Z.PV_CB_MaskExponentTables.c1
#print axioms R1Z.PV_CB_MaskExponentTables.mask
#print axioms R1Z.PV_CB_MaskExponentTables.read
#print axioms R1Z.PV_CB_MaskFillBody.c1
#print axioms R1Z.PV_CB_MaskFillBody.c1_reply
#print axioms R1Z.PV_CB_MaskFillBody.mask
#print axioms R1Z.PV_CB_MaskFillBody.mask_reply
#print axioms R1Z.PV_CB_MaskFillLoop.c1_finite
#print axioms R1Z.PV_CB_MaskFillLoop.c1_run
#print axioms R1Z.PV_CB_MaskFillLoop.mask_finite
#print axioms R1Z.PV_CB_MaskFillLoop.mask_run
#print axioms R1Z.PV_CB_MaskHorner.source
#print axioms R1Z.PV_CB_MaskIndices.coordinate
#print axioms R1Z.PV_CB_MaskIndices.factors_bound
#print axioms R1Z.PV_CB_MaskIndices.factors_read
#print axioms R1Z.PV_CB_MaskIndices.mask_factors_bound
#print axioms R1Z.PV_CB_MaskIndices.mask_factors_read
#print axioms R1Z.PV_CB_MaskLeaves.i
#print axioms R1Z.PV_CB_MaskLeaves.power
#print axioms R1Z.PV_CB_MaskLeaves.r
#print axioms R1Z.PV_CB_MaskLeaves.tower
#print axioms R1Z.PV_CB_MaskLinearsFinite.source
#print axioms R1Z.PV_CB_MaskRootEq.reference
#print axioms R1Z.PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value
#print axioms R1Z.PV_CB_Op100Exact.op100_source
#print axioms R1Z.PV_CB_Op101Exact.op101_source
#print axioms R1Z.PV_CB_Op105Exact.op105_source
#print axioms R1Z.PV_CB_Op107Exact.op107_source
#print axioms R1Z.PV_CB_Op107Transport.extracted_roundtrip
#print axioms R1Z.PV_CB_Op107Transport.native_roundtrip
#print axioms R1Z.PV_CB_Op109CanonicalBinding.reference_equation
#print axioms R1Z.PV_CB_Op109Exact.op109_source
#print axioms R1Z.PV_CB_Op109RefTransport.extracted_roundtrip
#print axioms R1Z.PV_CB_Op109RefTransport.native_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.extracted_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.extracted_wide_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.native_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.native_wide_roundtrip
#print axioms R1Z.PV_CB_Op110Source.op110_source
#print axioms R1Z.PV_CB_Op111Source.op111_source
#print axioms R1Z.PV_CB_Op114Source.op114_source
#print axioms R1Z.PV_CB_Op118Exact.op118_source
#print axioms R1Z.PV_CB_Op118Transport.extracted_array_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.extracted_points_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.extracted_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.native_array_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.native_points_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.native_roundtrip
#print axioms R1Z.PV_CB_Op127Source.op127_source
#print axioms R1Z.PV_CB_Op128Source.op128_source
#print axioms R1Z.PV_CB_Op130Source.op130_source
#print axioms R1Z.PV_CB_Op131Source.op131_source
#print axioms R1Z.PV_CB_Op223Boundary.no_universal_binding
#print axioms R1Z.PV_CB_Op223Boundary.reference_independent
#print axioms R1Z.PV_CB_Op223Callsite.array_agree
#print axioms R1Z.PV_CB_Op223Callsite.endpoint
#print axioms R1Z.PV_CB_Op223CanonicalCallsite.endpoint
#print axioms R1Z.PV_CB_Op223CanonicalDomain.reference
#print axioms R1Z.PV_CB_Op223CellSupport.cell
#print axioms R1Z.PV_CB_Op223Domain.array_domain
#print axioms R1Z.PV_CB_Op223Domain.len_val
#print axioms R1Z.PV_CB_Op223Domain.source_finite16
#print axioms R1Z.PV_CB_Op223ForestCallsite.endpoint
#print axioms R1Z.PV_CB_Op223ForestLocalCallsite.endpoint
#print axioms R1Z.PV_CB_Op223LaneAgreement.join
#print axioms R1Z.PV_CB_Op223LimbSupport.limb
#print axioms R1Z.PV_CB_Op223LocalCanonicalCallsite.endpoint
#print axioms R1Z.PV_CB_Op223ProducedCallsite.endpoint
#print axioms R1Z.PV_CB_Op223TagCanonical.canonical
#print axioms R1Z.PV_CB_Op223TagCanonical.expression
#print axioms R1Z.PV_CB_Op223TagCanonical.value
#print axioms R1Z.PV_CB_Op223TupleSupport.tuple
#print axioms R1Z.PV_CB_Op229Source.op229_source
#print axioms R1Z.PV_CB_Op71Exact.op71_source
#print axioms R1Z.PV_CB_Op72Exact.op72_source
#print axioms R1Z.PV_CB_Op77Source.op77_source
#print axioms R1Z.PV_CB_Op80Exact.op80_source
#print axioms R1Z.PV_CB_Op82Source.op82_source
#print axioms R1Z.PV_CB_Op83Source.op83_source
#print axioms R1Z.PV_CB_Op84Exact.op84_source
#print axioms R1Z.PV_CB_Op86Source.op86_source
#print axioms R1Z.PV_CB_OptionDiscriminant.none_tag
#print axioms R1Z.PV_CB_OptionDiscriminant.some_tag
#print axioms R1Z.PV_CB_OwnedMaskFill.c1
#print axioms R1Z.PV_CB_OwnedMaskFill.mask
#print axioms R1Z.PV_CB_OwnedMaskHorner.source
#print axioms R1Z.PV_CB_OwnedMaskHornerEq.source
#print axioms R1Z.PV_CB_OwnedMaskLeaves.mul_i
#print axioms R1Z.PV_CB_OwnedMaskLeaves.mul_r
#print axioms R1Z.PV_CB_OwnedMaskLeaves.tower
#print axioms R1Z.PV_CB_OwnedMaskLeaves.tower_total
#print axioms R1Z.PV_CB_OwnedMaskLinears.source
#print axioms R1Z.PV_CB_OwnedMaskLinearsEq.source
#print axioms R1Z.PV_CB_OwnedMaskTotal.total
#print axioms R1Z.PV_CB_PartialArrayUpdate.update
#print axioms R1Z.PV_CB_PartialForward.bind
#print axioms R1Z.PV_CB_PartialForward.finite
#print axioms R1Z.PV_CB_PreparedTotal.mul
#print axioms R1Z.PV_CB_PreparedTotal.mul_part
#print axioms R1Z.PV_CB_PreparedTotal.new
#print axioms R1Z.PV_CB_PreparedTotal.new_part
#print axioms R1Z.PV_CB_ProducerBind.bind
#print axioms R1Z.PV_CB_ProducerBind.inner
#print axioms R1Z.PV_CB_ProducerCallsite.endpoint
#print axioms R1Z.PV_CB_ProducerCell.cell
#print axioms R1Z.PV_CB_ProducerContext.cell_congr
#print axioms R1Z.PV_CB_ProducerContext.limb_congr
#print axioms R1Z.PV_CB_ProducerContext.tuple_congr
#print axioms R1Z.PV_CB_ProducerLimb.limb
#print axioms R1Z.PV_CB_ProducerLocalCallsite.endpoint
#print axioms R1Z.PV_CB_ProducerLocalCell.cell
#print axioms R1Z.PV_CB_ProducerLocalLimb.limb
#print axioms R1Z.PV_CB_ProducerLocalSelected.tuple
#print axioms R1Z.PV_CB_ProducerLocalTuple.tuple
#print axioms R1Z.PV_CB_ProducerMake16.valid
#print axioms R1Z.PV_CB_ProducerMetadataCarrier.limb
#print axioms R1Z.PV_CB_ProducerMetadataCarrier.limbs
#print axioms R1Z.PV_CB_ProducerOffsetChoice.canonical
#print axioms R1Z.PV_CB_ProducerOffsetChoice.cell
#print axioms R1Z.PV_CB_ProducerOffsetChoice.empty_valid
#print axioms R1Z.PV_CB_ProducerOffsetChoice.update
#print axioms R1Z.PV_CB_ProducerOffsetControl.finite
#print axioms R1Z.PV_CB_ProducerOffsetControl.run
#print axioms R1Z.PV_CB_ProducerOffsetControl.step_valid
#print axioms R1Z.PV_CB_ProducerOffsets.subtract
#print axioms R1Z.PV_CB_ProducerOffsets.zero_cell
#print axioms R1Z.PV_CB_ProducerOffsets.zero_limb
#print axioms R1Z.PV_CB_ProducerOffsets.zero_valid
#print axioms R1Z.PV_CB_ProducerPost.error
#print axioms R1Z.PV_CB_ProducerPost.pure
#print axioms R1Z.PV_CB_ProducerRead.array_mem
#print axioms R1Z.PV_CB_ProducerRead.reads
#print axioms R1Z.PV_CB_ProducerRead.slice_mem
#print axioms R1Z.PV_CB_ProducerRead.vec_mem
#print axioms R1Z.PV_CB_ProducerReadRestriction.cell
#print axioms R1Z.PV_CB_ProducerReadRestriction.limb
#print axioms R1Z.PV_CB_ProducerReadRestriction.tuple
#print axioms R1Z.PV_CB_ProducerReference.sampled
#print axioms R1Z.PV_CB_ProducerReference.slice_valid
#print axioms R1Z.PV_CB_ProducerSelected.successful_array
#print axioms R1Z.PV_CB_ProducerSelected.tuple
#print axioms R1Z.PV_CB_ProducerTraceData.reads
#print axioms R1Z.PV_CB_ProducerTraceData.successful_array
#print axioms R1Z.PV_CB_ProducerTry.bind
#print axioms R1Z.PV_CB_ProducerTuple.tuple
#print axioms R1Z.PV_CB_QuarticProjections.result_ext
#print axioms R1Z.PV_CB_QuarticProjections.value_ext
#print axioms R1Z.PV_CB_ReachBind.congr
#print axioms R1Z.PV_CB_ReverseWrap.pred_eq
#print axioms R1Z.PV_CB_TakeSource.op3_source
#print axioms R1Z.PV_CB_TowerLaneJoin.ext
#print axioms R1Z.PV_CB_TowerLaneJoin.successful
#print axioms R1Z.PV_CB_TupleProducerBody.source
#print axioms R1Z.PV_CB_TupleProducerCarrier.limb_valid
#print axioms R1Z.PV_CB_TupleProducerCarrier.limbs_valid
#print axioms R1Z.PV_CB_TupleProducerCarrier.produced
#print axioms R1Z.PV_CB_TupleProducerContract.source
#print axioms R1Z.PV_CB_TupleProducerInvariant.finite
#print axioms R1Z.PV_CB_TupleProducerInvariant.source
#print axioms R1Z.PV_CB_TupleProducerLoop.finite
#print axioms R1Z.PV_CB_TupleProducerLoop.source
#print axioms R1Z.PV_CB_TupleProducerMetadata.initial
#print axioms R1Z.PV_CB_TupleProducerMetadata.step
#print axioms R1Z.PV_CB_TupleProducerMetadataLoop.finite
#print axioms R1Z.PV_CB_TupleProducerMetadataLoop.source
#print axioms R1Z.PV_CB_TupleProducerMetadataRoot.source
#print axioms R1Z.PV_CB_TupleProducerOffset.canonical
#print axioms R1Z.PV_CB_TupleProducerOffset.initial
#print axioms R1Z.PV_CB_TupleProducerOffset.update
#print axioms R1Z.PV_CB_TupleProducerRoot.source
#print axioms R1Z.PV_CB_TupleProducerRootTotal.source
#print axioms R1Z.PV_CB_TupleProducerRow.source
#print axioms R1Z.PV_CB_TupleProducerScalar.canonical
#print axioms R1Z.PV_CB_TupleProducerScalar.sub
#print axioms R1Z.PV_CB_TupleProducerScalar.tweak_valid
#print axioms R1Z.PV_CB_TupleProducerScalar.zero_valid
#print axioms R1Z.PV_CB_TupleProducerSelectors.inhabited
#print axioms R1Z.PV_CB_TupleProducerSelectors.uniform
#print axioms R1Z.PV_CB_TupleProducerStep.valid
#print axioms R1Z.PV_CB_TupleProducerTotal.finite
#print axioms R1Z.PV_CB_TupleProducerTotal.source
#print axioms R1Z.PV_CB_TupleProducerTotal.step
#print axioms R1Z.PV_Join_AggregateCaller.dictionary
#print axioms R1Z.PV_Join_AggregateCaller.refinement_of_data
#print axioms R1Z.PV_Op134_ReferenceBundle.cells_reference
#print axioms R1Z.PV_Op134_ReferenceBundle.op134_reference
#print axioms R1Z.PV_Op134_ReferenceBundle.rows_reference
#print axioms R1Z.PV_Op223_Agreement.CM31_ZERO
#print axioms R1Z.PV_Op223_Agreement.CM31_add
#print axioms R1Z.PV_Op223_Agreement.CM31_from_m31
#print axioms R1Z.PV_Op223_Agreement.CM31_mul
#print axioms R1Z.PV_Op223_Agreement.CM31_mul_m31
#print axioms R1Z.PV_Op223_Agreement.CM31_sub
#print axioms R1Z.PV_Op223_Agreement.M31_ZERO
#print axioms R1Z.PV_Op223_Agreement.M31_add
#print axioms R1Z.PV_Op223_Agreement.M31_double
#print axioms R1Z.PV_Op223_Agreement.M31_mul
#print axioms R1Z.PV_Op223_Agreement.M31_reduce_u64
#print axioms R1Z.PV_Op223_Agreement.M31_sub
#print axioms R1Z.PV_Op223_Agreement.P
#print axioms R1Z.PV_Op223_Agreement.QM31_add
#print axioms R1Z.PV_Op223_Agreement.QM31_from_cm31
#print axioms R1Z.PV_Op223_Agreement.QM31_mul
#print axioms R1Z.PV_Op223_Agreement.QM31_mul_m31
#print axioms R1Z.PV_Op223_Agreement.ct_add
#print axioms R1Z.PV_Op223_Agreement.ct_reduce64
#print axioms R1Z.PV_Op223_Agreement.ct_sub
#print axioms R1Z.PV_Op223_Agreement.ct_subtract_p
#print axioms R1Z.PV_Op223_Agreement.mul_by_r
#print axioms R1Z.PV_Op223_Agreement.reduce_u64
#print axioms R1Z.PV_Op223_FieldBridge.CM31_mul_m31
#print axioms R1Z.PV_Op223_FieldBridge.QM31_add
#print axioms R1Z.PV_Op223_FieldBridge.QM31_from_cm31
#print axioms R1Z.PV_Op223_FieldBridge.QM31_mul
#print axioms R1Z.PV_Op223_FieldBridge.QM31_mul_m31
#print axioms R1Z.PV_Op223_FieldBridge.mul_by_r
#print axioms R1Z.PV_Op223_SelectedFields.add
#print axioms R1Z.PV_Op223_SelectedFields.cm_from
#print axioms R1Z.PV_Op223_SelectedFields.mul
#print axioms R1Z.PV_Op223_SelectedFields.qm_from
#print axioms R1Z.PV_Op223_SelectedFields.scale
#print axioms R1Z.PV_Op223_Source.P_source_p6
#print axioms R1Z.PV_Op223_Source.op223_p6
#print axioms R1Z.PV_Op223_Source.op223_source
#print axioms R1Z.PV_Op223_V164.refinement

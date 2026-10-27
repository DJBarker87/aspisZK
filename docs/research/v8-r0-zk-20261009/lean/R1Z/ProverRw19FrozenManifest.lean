import R1Z.ProverRw18AxiomsAudit
import R1Z.ProverRw19AssemblyCallerIff
import R1Z.ProverRw19AssemblyLength
import R1Z.ProverRw19AuditCaller
import R1Z.ProverRw19AuditData
import R1Z.ProverRw19AuditSource
import R1Z.ProverRw19AuditValue
import R1Z.ProverRw19BodyLength
import R1Z.ProverRw19BodyLengthValue
import R1Z.ProverRw19ByteLength
import R1Z.ProverRw19CachePreflight
import R1Z.ProverRw19CanonicalAuditCriterion
import R1Z.ProverRw19CanonicalAuditRefinement
import R1Z.ProverRw19LoopBind
import R1Z.ProverRw19MathematicalAssembly
import R1Z.ProverRw19MathematicalDataIff
import R1Z.ProverRw19MathematicalLength
import R1Z.ProverRw19OriginalAuditCriterion
import R1Z.ProverRw19OriginalBodyAudit
import R1Z.ProverRw19P6Caller
import R1Z.ProverRw19P6ContextIdentity
import R1Z.ProverRw19P6DataIff
import R1Z.ProverRw19P6Join
import R1Z.ProverRw19P6RawContextIdentity
import R1Z.ProverRw19PreparedAssembly
import R1Z.ProverRw19PublishLength
import R1Z.ProverRw19ReferenceLength
import R1Z.ProverRw19SelectedBodyLength
import R1Z.ProverRw19SelectedProofSize
import R1Z.ProverRw19SemanticLength
set_option autoImplicit false

-- Single cached component manifest and complete printed axioms audit.
-- The standalone audit attempt stopped on an absent transitive object.
-- Every actual audit command is replayed here after restoring that cache.
-- No deployed-release or whole-model byte-correspondence claim.

#check R1Z.ProverRw18ContextJoin.callback
#check R1Z.ProverRw19P6ContextIdentity.identity
#check R1Z.ProverRw19P6Join.callback
#check R1Z.ProverRw18ContextDataIff.criterion
#check R1Z.ProverRw19P6DataIff.criterion
#check R1Z.ProverRw19AssemblyCallerIff.criterion
#check R1Z.ProverRw19SelectedBodyLength.original
#check R1Z.ProverRw19PreparedAssembly.proofBytes
#check R1Z.ProverRw18ComponentGate.gate
#check R1Z.ProverRw18FixtureDecode.transfer
#check R1Z.ProverRw18FixtureDecode.withdrawal

#print axioms R1Z.ProverRw18ArithmeticBounds.canonical_scalar_product
#print axioms R1Z.ProverRw18ArithmeticBounds.canonical_sum
#print axioms R1Z.ProverRw18ArithmeticBounds.complex_product
#print axioms R1Z.ProverRw18ArithmeticBounds.product_bound
#print axioms R1Z.ProverRw18ArithmeticBounds.raw_scalar_product
#print axioms R1Z.ProverRw18ArrayValues.input
#print axioms R1Z.ProverRw18ArrayValues.ofFn
#print axioms R1Z.ProverRw18CallbackModel.value
#print axioms R1Z.ProverRw18CallbackWrite.bytes
#print axioms R1Z.ProverRw18CallbackWrite.image
#print axioms R1Z.ProverRw18CanonicalBytes.field_image
#print axioms R1Z.ProverRw18CanonicalBytes.image
#print axioms R1Z.ProverRw18Checkpoint.resume
#print axioms R1Z.ProverRw18Checkpoint.split
#print axioms R1Z.ProverRw18CodecDecode.canonical
#print axioms R1Z.ProverRw18CodecDecode.field
#print axioms R1Z.ProverRw18CodecDecode.fixed
#print axioms R1Z.ProverRw18CodecGroups.grouped
#print axioms R1Z.ProverRw18ComplexBytes.exact_write
#print axioms R1Z.ProverRw18ComplexBytes.length
#print axioms R1Z.ProverRw18ComplexBytes.output_value
#print axioms R1Z.ProverRw18ComplexRegion.exact_write
#print axioms R1Z.ProverRw18ComplexWrite.context
#print axioms R1Z.ProverRw18ComplexWrite.exact_write
#print axioms R1Z.ProverRw18ComplexWrite.word_length
#print axioms R1Z.ProverRw18ComponentGate.gate
#print axioms R1Z.ProverRw18CompressionDecode.exact_decode
#print axioms R1Z.ProverRw18CompressionWrite.bytes
#print axioms R1Z.ProverRw18CompressionWrite.exact_write
#print axioms R1Z.ProverRw18ContextBounded.body_native
#print axioms R1Z.ProverRw18ContextBounded.bounded
#print axioms R1Z.ProverRw18ContextBranch.none
#print axioms R1Z.ProverRw18ContextBranch.some
#print axioms R1Z.ProverRw18ContextCaller.caller
#print axioms R1Z.ProverRw18ContextCompression.combined
#print axioms R1Z.ProverRw18ContextCompression.owned
#print axioms R1Z.ProverRw18ContextData.refinement
#print axioms R1Z.ProverRw18ContextDataIff.criterion
#print axioms R1Z.ProverRw18ContextErrors.add_failure
#print axioms R1Z.ProverRw18ContextErrors.power_divergence
#print axioms R1Z.ProverRw18ContextErrors.power_failure
#print axioms R1Z.ProverRw18ContextErrors.scale_failure
#print axioms R1Z.ProverRw18ContextFuel.arity16
#print axioms R1Z.ProverRw18ContextFuel.gate_bound
#print axioms R1Z.ProverRw18ContextFuel.sufficient
#print axioms R1Z.ProverRw18ContextInduction.run
#print axioms R1Z.ProverRw18ContextJoin.callback
#print axioms R1Z.ProverRw18ContextJoin.dictionaries
#print axioms R1Z.ProverRw18ContextReference.compress
#print axioms R1Z.ProverRw18ContextReference.loop
#print axioms R1Z.ProverRw18ContextStep.body
#print axioms R1Z.ProverRw18ContextSuffix.owned
#print axioms R1Z.ProverRw18ContextSuffix.value
#print axioms R1Z.ProverRw18ContextTotal.arity16
#print axioms R1Z.ProverRw18ContextTotal.paired_total
#print axioms R1Z.ProverRw18ContextTotal.total
#print axioms R1Z.ProverRw18CopyArray.closed
#print axioms R1Z.ProverRw18CopyArray.context
#print axioms R1Z.ProverRw18CopyArrayBytes.image
#print axioms R1Z.ProverRw18CopyArrayWide.value
#print axioms R1Z.ProverRw18CopyCarrier.closed
#print axioms R1Z.ProverRw18CopyCarrier.context
#print axioms R1Z.ProverRw18CopyCongruence.closed
#print axioms R1Z.ProverRw18CopyCongruence.context
#print axioms R1Z.ProverRw18CopyPolynomial.value
#print axioms R1Z.ProverRw18CopyReference.closed
#print axioms R1Z.ProverRw18CopyReference.context
#print axioms R1Z.ProverRw18CopyReference.input_values
#print axioms R1Z.ProverRw18CopySpecialized.copy
#print axioms R1Z.ProverRw18CopyTaggedReference.closed
#print axioms R1Z.ProverRw18CopyTaggedReference.context
#print axioms R1Z.ProverRw18CopyTags.canonical
#print axioms R1Z.ProverRw18CopyTags.range
#print axioms R1Z.ProverRw18CopyTags.word_canonical
#print axioms R1Z.ProverRw18CopyTags.word_val
#print axioms R1Z.ProverRw18CopyWide.value
#print axioms R1Z.ProverRw18FieldBytes.encoded
#print axioms R1Z.ProverRw18FieldBytes.words
#print axioms R1Z.ProverRw18FieldCompression.context
#print axioms R1Z.ProverRw18FieldCompression.owned
#print axioms R1Z.ProverRw18FieldEncode.canonical
#print axioms R1Z.ProverRw18FieldEncode.decoded
#print axioms R1Z.ProverRw18FieldEncode.encoded
#print axioms R1Z.ProverRw18FieldEncode.word_canonical
#print axioms R1Z.ProverRw18FieldEncode.word_decoded
#print axioms R1Z.ProverRw18FieldEncode.word_val
#print axioms R1Z.ProverRw18FieldFiniteSum.eval_ofFn
#print axioms R1Z.ProverRw18FieldFixtures.lambda_canonical
#print axioms R1Z.ProverRw18FieldFixtures.transfer
#print axioms R1Z.ProverRw18FieldFixtures.transfer_lambda
#print axioms R1Z.ProverRw18FieldFixtures.withdrawal
#print axioms R1Z.ProverRw18FieldFixtures.withdrawal_lambda
#print axioms R1Z.ProverRw18FieldFold.fold
#print axioms R1Z.ProverRw18FieldInitial.canonical
#print axioms R1Z.ProverRw18FieldInitial.decoded
#print axioms R1Z.ProverRw18FieldInitial.full_base
#print axioms R1Z.ProverRw18FieldInjective.full
#print axioms R1Z.ProverRw18FieldInjective.raw
#print axioms R1Z.ProverRw18FieldInjective.word
#print axioms R1Z.ProverRw18FieldMeaning.add
#print axioms R1Z.ProverRw18FieldMeaning.mul
#print axioms R1Z.ProverRw18FieldMeaning.scale
#print axioms R1Z.ProverRw18FieldModel.append
#print axioms R1Z.ProverRw18FieldModel.output
#print axioms R1Z.ProverRw18FieldModel.power
#print axioms R1Z.ProverRw18FieldPower.projection
#print axioms R1Z.ProverRw18FieldPower.run
#print axioms R1Z.ProverRw18FieldPowerPure.fold_equal
#print axioms R1Z.ProverRw18FieldPowerPure.projection
#print axioms R1Z.ProverRw18FieldReference.closed
#print axioms R1Z.ProverRw18FieldReference.context
#print axioms R1Z.ProverRw18FieldStateReference.combined
#print axioms R1Z.ProverRw18FieldStateReference.owned
#print axioms R1Z.ProverRw18FieldStep.step
#print axioms R1Z.ProverRw18FieldSuffix.control
#print axioms R1Z.ProverRw18FieldSuffix.field
#print axioms R1Z.ProverRw18FinalPower16.combined
#print axioms R1Z.ProverRw18FinalPower16.exact_power
#print axioms R1Z.ProverRw18FixtureDecode.transfer
#print axioms R1Z.ProverRw18FixtureDecode.withdrawal
#print axioms R1Z.ProverRw18FixturePolynomial.transfer
#print axioms R1Z.ProverRw18FixturePolynomial.withdrawal
#print axioms R1Z.ProverRw18FixturePower.transfer
#print axioms R1Z.ProverRw18FixturePower.withdrawal
#print axioms R1Z.ProverRw18FixtureSamples.transfer_context
#print axioms R1Z.ProverRw18FixtureSamples.transfer_nonempty
#print axioms R1Z.ProverRw18FixtureSamples.withdrawal_context
#print axioms R1Z.ProverRw18FixtureSamples.withdrawal_nonempty
#print axioms R1Z.ProverRw18FixtureWrite.transfer
#print axioms R1Z.ProverRw18FixtureWrite.withdrawal
#print axioms R1Z.ProverRw18FoldAppend.div_prefix
#print axioms R1Z.ProverRw18FoldAppend.fail_prefix
#print axioms R1Z.ProverRw18FoldAppend.owned
#print axioms R1Z.ProverRw18FoldAppend.run
#print axioms R1Z.ProverRw18FullCarrier.canonical_encode
#print axioms R1Z.ProverRw18FullCarrier.encode_value
#print axioms R1Z.ProverRw18FullCarrier.full_raw
#print axioms R1Z.ProverRw18FullCarrier.raw_full
#print axioms R1Z.ProverRw18FullCarrier.value_encode
#print axioms R1Z.ProverRw18FullCarrier.value_injective
#print axioms R1Z.ProverRw18GenericPolynomial.copy
#print axioms R1Z.ProverRw18GenericPolynomial.ofFn
#print axioms R1Z.ProverRw18HornerBridge.eval
#print axioms R1Z.ProverRw18InlineContext.unfold_run
#print axioms R1Z.ProverRw18LambdaEdges.base_encoded
#print axioms R1Z.ProverRw18LambdaEdges.eval_one
#print axioms R1Z.ProverRw18LambdaEdges.one
#print axioms R1Z.ProverRw18LambdaEdges.zero
#print axioms R1Z.ProverRw18LiftTyped.emittedC_roundtrip
#print axioms R1Z.ProverRw18LiftTyped.emittedQ_roundtrip
#print axioms R1Z.ProverRw18LiftTyped.fullC_roundtrip
#print axioms R1Z.ProverRw18LiftTyped.fullQ_roundtrip
#print axioms R1Z.ProverRw18LiftTyped.initial
#print axioms R1Z.ProverRw18LiftTyped.transport
#print axioms R1Z.ProverRw18LoopCarrier.value
#print axioms R1Z.ProverRw18OriginalLift.context
#print axioms R1Z.ProverRw18OriginalLift.initial
#print axioms R1Z.ProverRw18OriginalLift.owned
#print axioms R1Z.ProverRw18Overlay.adjacent
#print axioms R1Z.ProverRw18Overlay.zero
#print axioms R1Z.ProverRw18PolynomialAppend.eval
#print axioms R1Z.ProverRw18PolynomialAppend.value
#print axioms R1Z.ProverRw18QuarticBytes.exact_write
#print axioms R1Z.ProverRw18QuarticBytes.length
#print axioms R1Z.ProverRw18QuarticBytes.output_value
#print axioms R1Z.ProverRw18QuarticWrite.context
#print axioms R1Z.ProverRw18QuarticWrite.exact_write
#print axioms R1Z.ProverRw18SliceWrite.exact_write
#print axioms R1Z.ProverRw18SuffixFormula.exact_run
#print axioms R1Z.ProverRw18WriterContext.bytes
#print axioms R1Z.ProverRw18WriterContext.closed
#print axioms R1Z.ProverRw18WriterDecode.exact_decode
#print axioms R1Z.ProverRw19AssemblyCallerIff.criterion
#print axioms R1Z.ProverRw19AssemblyLength.assemble
#print axioms R1Z.ProverRw19AuditCaller.good
#print axioms R1Z.ProverRw19AuditCaller.audit
#print axioms R1Z.ProverRw19AuditData.bytes
#print axioms R1Z.ProverRw19AuditData.audit_of_bytes
#print axioms R1Z.ProverRw19AuditData.data_of_bytes
#print axioms R1Z.ProverRw19AuditSource.continuation
#print axioms R1Z.ProverRw19AuditSource.body
#print axioms R1Z.ProverRw19AuditValue.guarded
#print axioms R1Z.ProverRw19AuditValue.bind_good
#print axioms R1Z.ProverRw19AuditValue.rejected
#print axioms R1Z.ProverRw19AuditValue.successful
#print axioms R1Z.ProverRw19AuditValue.residual
#print axioms R1Z.ProverRw19BodyLength.continuation
#print axioms R1Z.ProverRw19BodyLength.body
#print axioms R1Z.ProverRw19BodyLengthValue.bind_good
#print axioms R1Z.ProverRw19BodyLengthValue.finish_good
#print axioms R1Z.ProverRw19BodyLengthValue.rejected
#print axioms R1Z.ProverRw19BodyLengthValue.residual
#print axioms R1Z.ProverRw19ByteLength.bind_good
#print axioms R1Z.ProverRw19ByteLength.guarded
#print axioms R1Z.ProverRw19ByteLength.successful
#print axioms R1Z.ProverRw19ByteLength.residual
#print axioms R1Z.ProverRw19P6RawContextIdentity.identity
#print axioms R1Z.ProverRw19CanonicalAuditCriterion.data_iff
#print axioms R1Z.ProverRw19CanonicalAuditCriterion.result_iff
#print axioms R1Z.ProverRw19CanonicalAuditRefinement.refinement
#print axioms R1Z.ProverRw19LoopBind.loop_bind
#print axioms R1Z.ProverRw19MathematicalAssembly.error
#print axioms R1Z.ProverRw19MathematicalAssembly.byte
#print axioms R1Z.ProverRw19MathematicalAssembly.proofBytes
#print axioms R1Z.ProverRw19MathematicalAssembly.output
#print axioms R1Z.ProverRw19MathematicalAssembly.bytes
#print axioms R1Z.ProverRw19MathematicalDataIff.criterion
#print axioms R1Z.ProverRw19MathematicalLength.proof
#print axioms R1Z.ProverRw19OriginalAuditCriterion.criterion
#print axioms R1Z.ProverRw19OriginalBodyAudit.criterion
#print axioms R1Z.ProverRw19P6Caller.caller
#print axioms R1Z.ProverRw19P6ContextIdentity.identity
#print axioms R1Z.ProverRw19P6DataIff.criterion
#print axioms R1Z.ProverRw19P6Join.callback
#print axioms R1Z.ProverRw19P6Join.dictionaries
#print axioms R1Z.ProverRw19P6RawContextIdentity.listRun
#print axioms R1Z.ProverRw19P6RawContextIdentity.loop
#print axioms R1Z.ProverRw19P6RawContextIdentity.context_eq_source
#print axioms R1Z.ProverRw19PreparedAssembly.proofBytes
#print axioms R1Z.ProverRw19PreparedAssembly.output
#print axioms R1Z.ProverRw19PreparedAssembly.failure
#print axioms R1Z.ProverRw19PreparedAssembly.divergence
#print axioms R1Z.ProverRw19PreparedAssembly.rejected
#print axioms R1Z.ProverRw19PreparedAssembly.length
#print axioms R1Z.ProverRw19PublishLength.publish
#print axioms R1Z.ProverRw19AssemblyLength.reference
#print axioms R1Z.ProverRw19SelectedBodyLength.original
#print axioms R1Z.ProverRw19SelectedProofSize.original
#print axioms R1Z.ProverRw19SelectedProofSize.closed
#print axioms R1Z.ProverRw19SemanticLength.proof

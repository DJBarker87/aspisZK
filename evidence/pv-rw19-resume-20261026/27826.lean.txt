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

-- Cached component axioms audit; not a deployed release theorem.
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
#print axioms R1Z.ProverRw18ArithmeticBounds.product_bound
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

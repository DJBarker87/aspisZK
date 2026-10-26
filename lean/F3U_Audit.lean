import F3U_AccountEndpoint
import F3U_AccountEvent
import F3U_AllWorldMachine
import F3U_AllWorldPrepare
import F3U_AllWorldPreparedValue
import F3U_AsSliceBytes
import F3U_Averaging
import F3U_Boundary
import F3U_BridgeAudit
import F3U_BytePreparation
import F3U_CanonicalNative
import F3U_CollisionJoin
import F3U_ConditionalBound
import F3U_ConditionalRange
import F3U_Decode
import F3U_ExtractorOrCollision
import F3U_FirstCode
import F3U_FirstHead
import F3U_FirstInstances
import F3U_FirstSkeleton
import F3U_InitAddress
import F3U_InitCall
import F3U_InstalledHead
import F3U_Joint
import F3U_LedgerBaseline
import F3U_LoweredHead
import F3U_NativeLog
import F3U_Numeric
import F3U_Oracle
import F3U_OracleHead
import F3U_OracleSeparation
import F3U_OwnerAudit
import F3U_PairInputs
import F3U_PairLog
import F3U_Pointwise
import F3U_PrepareHead
import F3U_PublicHead
import F3U_PublicOracleValue
import F3U_Range
import F3U_RangeChord
import F3U_RangeEdges
import F3U_RangeMaximal
import F3U_RangeOld
import F3U_RangePolynomial
import F3U_ReaderCode
import F3U_Recovered
import F3U_Rehash
import F3U_RehashBind
import F3U_RehashInit
import F3U_RehashPublic
import F3U_RehashValue
import F3U_ReifyExact
import F3U_ReifyFirst
import F3U_ReifyLog
import F3U_ReifyValue
import F3U_RuntimeMass
import F3U_RuntimePointwise
import F3U_SamePair
import F3U_SecondCode
import F3U_SecondInstances
import F3U_SecondSkeleton
import F3U_SemanticBytes
import F3U_SemanticHead
import F3U_Slice
import F3U_SourceCost
import F3U_SourceInputs
import F3U_SubmissionIdentity
import F3U_TwoPass
import F3U_UnitMass
import F3U_VerifyHead

#print axioms AspisR1.F3U_AccountEndpoint.bound
#print axioms AspisR1.F3U_AccountEvent.charged
#print axioms AspisR1.F3U_AllWorldMachine.accepted
#print axioms AspisR1.F3U_AllWorldPrepare.accepted
#print axioms AspisR1.F3U_AllWorldPreparedValue.accepted
#print axioms AspisR1.F3U_AsSliceBytes.byte
#print axioms AspisR1.F3U_AsSliceBytes.inverse
#print axioms AspisR1.F3U_Averaging.charge
#print axioms AspisR1.F3U_Boundary.installed
#print axioms AspisR1.F3U_BytePreparation.accepted
#print axioms AspisR1.F3U_CanonicalNative.joined
#print axioms AspisR1.F3U_CollisionJoin.carried
#print axioms AspisR1.F3U_ConditionalBound.bound
#print axioms AspisR1.F3U_ConditionalRange.claims
#print axioms AspisR1.F3U_Decode.same
#print axioms AspisR1.F3U_ExtractorOrCollision.extractor
#print axioms AspisR1.F3U_FirstCode.same
#print axioms AspisR1.F3U_FirstHead.first
#print axioms AspisR1.F3U_FirstInstances.native
#print axioms AspisR1.F3U_FirstInstances.retained
#print axioms AspisR1.F3U_InitAddress.head
#print axioms AspisR1.F3U_InitCall.reached
#print axioms AspisR1.F3U_InstalledHead.head
#print axioms AspisR1.F3U_Joint.output
#print axioms AspisR1.F3U_LoweredHead.first
#print axioms AspisR1.F3U_NativeLog.same
#print axioms AspisR1.F3U_Numeric.exact
#print axioms AspisR1.F3U_Numeric.positive
#print axioms AspisR1.F3U_Numeric.runtime_margin
#print axioms AspisR1.F3U_Oracle.decoded
#print axioms AspisR1.F3U_Oracle.syscall
#print axioms AspisR1.F3U_OracleHead.answer
#print axioms AspisR1.F3U_OracleSeparation.cannot_fix_oracle
#print axioms AspisR1.F3U_OracleSeparation.same_on_return
#print axioms AspisR1.F3U_PairInputs.accepted
#print axioms AspisR1.F3U_PairLog.evaluated
#print axioms AspisR1.F3U_Pointwise.failure_charge
#print axioms AspisR1.F3U_PrepareHead.reached
#print axioms AspisR1.F3U_PublicHead.first
#print axioms AspisR1.F3U_PublicOracleValue.initial
#print axioms AspisR1.F3U_PublicOracleValue.public_value
#print axioms AspisR1.F3U_Range.next_fails
#print axioms AspisR1.F3U_Range.per_attempt
#print axioms AspisR1.F3U_RangeChord.chord
#print axioms AspisR1.F3U_RangeEdges.edges
#print axioms AspisR1.F3U_RangeMaximal.beyond
#print axioms AspisR1.F3U_RangeMaximal.exact_range
#print axioms AspisR1.F3U_RangeOld.original_model_range_fails
#print axioms AspisR1.F3U_RangePolynomial.total_gap
#print axioms AspisR1.F3U_ReaderCode.same
#print axioms AspisR1.F3U_Recovered.inputs_or_collision
#print axioms AspisR1.F3U_Rehash.associated
#print axioms AspisR1.F3U_Rehash.lowered
#print axioms AspisR1.F3U_RehashBind.bind
#print axioms AspisR1.F3U_RehashBind.digest
#print axioms AspisR1.F3U_RehashBind.lift
#print axioms AspisR1.F3U_RehashInit.same
#print axioms AspisR1.F3U_RehashPublic.same
#print axioms AspisR1.F3U_RehashValue.value
#print axioms AspisR1.F3U_ReifyExact.exact
#print axioms AspisR1.F3U_ReifyFirst.first
#print axioms AspisR1.F3U_ReifyLog.log
#print axioms AspisR1.F3U_ReifyValue.value
#print axioms AspisR1.F3U_RuntimeMass.charge
#print axioms AspisR1.F3U_RuntimePointwise.charge
#print axioms AspisR1.F3U_SamePair.accepted_pair
#print axioms AspisR1.F3U_SecondCode.common
#print axioms AspisR1.F3U_SecondCode.same
#print axioms AspisR1.F3U_SecondInstances.native
#print axioms AspisR1.F3U_SecondInstances.retained
#print axioms AspisR1.F3U_SemanticBytes.encoded
#print axioms AspisR1.F3U_SemanticHead.first
#print axioms AspisR1.F3U_Slice.decode_encode
#print axioms AspisR1.F3U_Slice.roundtrip
#print axioms AspisR1.F3U_SourceCost.cost_or_collision
#print axioms AspisR1.F3U_SourceInputs.accepted
#print axioms AspisR1.F3U_SubmissionIdentity.ext
#print axioms AspisR1.F3U_SubmissionIdentity.transport
#print axioms AspisR1.F3U_TwoPass.annotated_or_collision
#print axioms AspisR1.F3U_UnitMass.failure_le_one
#print axioms AspisR1.F3U_UnitMass.rejected
#print axioms AspisR1.F3U_UnitMass.runtime_le_one
#print axioms AspisR1.F3U_VerifyHead.first

import S8JoinAccumulatorStage
import S8JoinCompactChunks
import S8JoinCompactTotal
import S8JoinFinishExact
import S8JoinFinishField
import S8JoinFrozenArithmetic
import S8JoinFrozenScan
import S8JoinModelRepresentation
import S8JoinRawCongruence
import S8JoinS7Reference
import S8JoinScanRemainder

/-! Final focused additive packet audit. This does not assert the missing Rust caller join. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinPacketAudit

theorem checked_reference :
    S8Kani2CallerJoin.P6Certificate ∧
    S8JoinFrozenArithmetic.decision=OraclePortFrozenOrder.dV_frozen ∧
    ∀ b : Aeneas.Std.Slice Aeneas.Std.U8,
      S8OwnedP6.check_values_owned b=Aeneas.Std.Result.ok
        (S8JoinCompactTotal.scanResult (S8JoinCompactChunks.wire b)) :=
  ⟨S8Kani2CallerJoin.p6_certificate,S8JoinFrozenArithmetic.decision_eq,
    S8JoinCompactTotal.check_values_total⟩

#print axioms checked_reference
#print axioms AspisR1.S8JoinAccumulatorStage.finish_check
#print axioms AspisR1.S8JoinCompactChunks.little_four
#print axioms AspisR1.S8JoinCompactChunks.codec_canonical
#print axioms AspisR1.S8JoinCompactChunks.slice_slice
#print axioms AspisR1.S8JoinCompactChunks.array_wire
#print axioms AspisR1.S8JoinCompactChunks.chunk_iff
#print axioms AspisR1.S8JoinCompactChunks.canonical_chunks
#print axioms AspisR1.S8JoinCompactTotal.consumed_length
#print axioms AspisR1.S8JoinCompactTotal.consumed_slice
#print axioms AspisR1.S8JoinCompactTotal.consumed_chunks
#print axioms AspisR1.S8JoinCompactTotal.check_values_total
#print axioms AspisR1.S8JoinCompactTotal.aligned_scan_total
#print axioms S8JoinFinishExact.prefix_length
#print axioms S8JoinFinishExact.reference_exact
#print axioms S8JoinFinishExact.mutable_exact
#print axioms AspisR1.S8JoinFinishField.modelValue_field
#print axioms AspisR1.S8JoinFinishField.finish_field
#print axioms AspisR1.S8JoinFinishField.mutable_field
#print axioms AspisR1.S8JoinFrozenArithmetic.verify_eq
#print axioms AspisR1.S8JoinFrozenArithmetic.arithmetic_eq
#print axioms AspisR1.S8JoinFrozenArithmetic.decision_eq
#print axioms AspisR1.S8JoinFrozenArithmetic.accepted_reference
#print axioms AspisR1.S8JoinFrozenArithmetic.accepted_model_caller
#print axioms AspisR1.S8JoinFrozenScan.segment_wire
#print axioms AspisR1.S8JoinFrozenScan.parse_scan
#print axioms AspisR1.S8JoinFrozenScan.parsed_y1
#print axioms AspisR1.S8JoinFrozenScan.accepted_y1
#print axioms AspisR1.S8JoinModelRepresentation.row_limb
#print axioms AspisR1.S8JoinModelRepresentation.row_field
#print axioms AspisR1.S8JoinModelRepresentation.raw_row
#print axioms AspisR1.S8JoinModelRepresentation.model_caller
#print axioms AspisR1.S8JoinModelRepresentation.model_finish_check
#print axioms AspisR1.S8JoinModelRepresentation.model_check_eq
#print axioms AspisR1.S8JoinRawCongruence.raw_mod_eq
#print axioms AspisR1.S8JoinRawCongruence.modelValue_eq
#print axioms AspisR1.S8JoinRawCongruence.output_eq
#print axioms AspisR1.S8JoinRawCongruence.finish_eq
#print axioms AspisR1.S8JoinRawCongruence.mutable_finish_eq
#print axioms AspisR1.S8JoinS7Reference.weights_eq
#print axioms AspisR1.S8JoinS7Reference.reached_caller
#print axioms AspisR1.S8JoinS7Reference.finish_check
#print axioms AspisR1.S8JoinS7Reference.mutable_finish
#print axioms AspisR1.S8JoinScanRemainder.short_scan
#print axioms AspisR1.S8JoinScanRemainder.unaligned_mismatch
end AspisR1.S8JoinPacketAudit
end

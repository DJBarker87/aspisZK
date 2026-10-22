import OraclePortCkptAbi4Interleaved
import OraclePortCkptAbi4Std
import OraclePortCkptAbi4Decode

/-! Focused union only. No full frozen dependency replay or source cone join. -/
#print axioms AspisR1.OraclePortCkptAbi4Interleaved.interleaved_length
#print axioms AspisR1.OraclePortCkptAbi4Interleaved.interleaved_not_erased
#print axioms AspisR1.OraclePortCkptAbi4Std.shared_interval
#print axioms AspisR1.OraclePortCkptAbi4Std.shared_exhausted
#print axioms AspisR1.OraclePortCkptAbi4Std.mutable_writeback
#print axioms AspisR1.OraclePortCkptAbi4Std.no_requested_capacity
#print axioms AspisR1.OraclePortCkptAbi4Decode.decoded_canonical
#print axioms AspisR1.OraclePortCkptAbi4Decode.from_limbs_canonical
#print axioms AspisR1.OraclePortCkptAbi4Decode.decoded_wide_canonical
#print axioms AspisR1.OraclePortCkptAbi4Decode.canonical_words_bytes

import NDO_JFo_Tail
import NDO_JFo_DecodedAccumulator
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_ReaderFixture
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- Partial real-byte non-vacuity: the complete native reader tail and
physical accumulator decoder agree. This makes no hash-prefix, TX1-save,
TX2-wrapper, batch, query or finish acceptance assertion. -/
theorem inhabited : ∃ p : verifier.Prepared, ∃ a : verifier.Accumulator,
    a.next=10#usize ∧ a.weights.val.length=64 ∧
    Port4A_NativeReader.tail (T2Nat_ReaderOps.ops true)
      JFx_NativeBytes.checkpoint .S2 10#u8 1736#usize
      (JFq_Range.segment 1736 32 (by decide)) JFo_AuthBytes.checksum=ok (.Ok (p,a)) ∧
    OraclePortCheckpointResumeC5.decodeAccumulator (MultiproofConeCanonical.bytesOf JFx_NativeBytes.checkpoint.val)=
      some (CheckpointBytes5Output.accumulator a) := by
  exact ⟨JFo_Prepared.value,JFo_Prepared.accumulator,rfl,JFo_Weights.length,
    JFo_Tail.native,JFo_DecodedAccumulator.source⟩

#print axioms inhabited
#print inhabited
end AspisR1.JFo_ReaderFixture
end

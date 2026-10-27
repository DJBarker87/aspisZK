import RPz7_S6CurrentCodecInstallationV1
import RPz7_S6OuterNativeEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6CurrentCodecInstallation
open AspisS6CurrentAdapterCarrier AspisS6OuterNativeOps

theorem decode_total (bytes : Slice U8) : ∃ result,decode bytes=ok result := by
  obtain ⟨result,run⟩ := AspisS6NativeForestDecode.decode_total bytes
  unfold decode
  rw [boxed_eq]
  simp only [boxOps,rawDecoder,run]
  cases result <;> exact ⟨_,rfl⟩

theorem encode_total (statement : Statement) : ∃ result,encode statement=ok result := by
  obtain ⟨result,run⟩ := AspisS6OuterNativeEncodeTotal.encode_total (toPoolV1PairForestTerminalStatementV1 statement)
  unfold encode
  rw [run]
  exact ⟨_,rfl⟩

theorem accepted_inverse (bytes : Slice U8) (statement : Statement)
    (decoded : decode bytes=ok (.Ok statement)) :
    ∃ encoded : Array U8 1880#usize,encode statement=ok (.Ok encoded) ∧ encoded.val=bytes.val := by
  obtain ⟨encoded,run,contents⟩ := AspisS6OuterNativeCodec.accepted_inverse bytes
    (toPoolV1PairForestTerminalStatementV1 statement) (decode_success bytes statement decoded)
  refine ⟨encoded,?_,contents⟩
  unfold encode
  rw [run]
  rfl

#print axioms decode_total
#print axioms encode_total
#print axioms accepted_inverse
end AspisS6CurrentCodecInstallation

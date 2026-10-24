import S6NativePaymentAcceptedInverseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativePaymentContents
open AspisR1TerminalDecoder
open pool_v1.payment_relation

theorem transfer_accepted_roundtrip (bytes : Slice U8) (value : PoolV1PrivateTransferPublicV1)
    (encoded : Array U8 216#usize)
    (decoded : decode_pool_v1_private_transfer_public_v1 bytes=ok (core.result.Result.Ok value))
    (encoded_actual : encode_pool_v1_private_transfer_public_v1 value=ok (core.result.Result.Ok encoded)) :
    encoded.val=bytes.val := by
  obtain ⟨actual,contents,run⟩ := transfer_accepted_inverse bytes value decoded
  rw [encoded_actual] at run
  cases run
  exact contents

#print axioms transfer_accepted_roundtrip

theorem withdrawal_accepted_roundtrip (bytes : Slice U8) (value : PoolV1WithdrawalPublicV1)
    (encoded : Array U8 216#usize)
    (decoded : decode_pool_v1_withdrawal_public_v1 bytes=ok (core.result.Result.Ok value))
    (encoded_actual : encode_pool_v1_withdrawal_public_v1 value=ok (core.result.Result.Ok encoded)) :
    encoded.val=bytes.val := by
  obtain ⟨actual,contents,run⟩ := withdrawal_accepted_inverse bytes value decoded
  rw [encoded_actual] at run
  cases run
  exact contents

#print axioms withdrawal_accepted_roundtrip

end AspisS6NativePaymentContents

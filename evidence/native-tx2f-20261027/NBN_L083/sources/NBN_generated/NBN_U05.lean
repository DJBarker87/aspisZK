import NBN_StatementEncoderSummary
import NBN_U03
set_option autoImplicit false
noncomputable section
namespace NBN_U05
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open NBN_StatementResult NBN_ValidatorSummary

theorem conditional (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult)
    (NBN_Dep_DigestEncodeRaw : NBN_DigestResultDependency.NBN_Dep_DigestEncodeRaw enc)
    (NBN_Dep_TransferEncode : NBN_ValidatorSummary.NBN_Dep_TransferEncode t)
    (NBN_Dep_WithdrawalEncode : NBN_ValidatorSummary.NBN_Dep_WithdrawalEncode w) :
    (∀ s, NBN_ValidatorSummary.run enc t w s =
      pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s) ∧
    (∀ s, NBN_StatementEncoderSummary.run enc t w s =
      NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s)) :=
  ⟨NBN_ValidatorSummary.source enc t w (fun d _ => NBN_Dep_DigestEncodeRaw d)
      NBN_Dep_TransferEncode NBN_Dep_WithdrawalEncode,
    NBN_StatementEncoderSummary.source enc t w NBN_Dep_DigestEncodeRaw
      NBN_Dep_TransferEncode NBN_Dep_WithdrawalEncode⟩

/-- The SAME fifth tuple component reaches the validator's output-lane child. -/
theorem validator_nullifier (s : Statement) :
    (parts s).2.2.2.2.1 = match s with
      | .PrivateTransfer _ p => p.nullifier
      | .Withdrawal _ p => p.nullifier := NBD_TerminalProjection.nullifier_same s

/-- The SAME variant selects the actual encoder prefix tag. -/
theorem encoder_kind (s : Statement) : NBN_EncoderBytes.tag s = match s with
    | .PrivateTransfer _ _ => 1#u8
    | .Withdrawal _ _ => 2#u8 := by cases s <;> rfl

#print axioms conditional
#print axioms validator_nullifier
#print axioms encoder_kind
end NBN_U05

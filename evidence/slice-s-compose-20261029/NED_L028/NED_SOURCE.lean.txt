import NBN_U05
import NBP_DigestEncode
import NBP_TransferEncode
import NBP_WithdrawalEncode
set_option autoImplicit false
noncomputable section
namespace NED_CodecComposition
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

/-- Total raw law; hence also valid at every canonical digest call site. -/
theorem digest_raw : NBN_DigestResultDependency.NBN_Dep_DigestEncodeRaw
    atomic_statement.encode_digest_canonical := NBP_DigestEncode.result

theorem digest_canonical : NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical
    atomic_statement.encode_digest_canonical := fun d _ => digest_raw d

/-- The safe payment reference returns the exact emitted Result on every
    typed payment, including rejection; no payment acceptance is assumed. -/
theorem transfer_law : NBN_ValidatorSummary.NBN_Dep_TransferEncode
    (fun p => ok (NBP_PaymentModel.transfer_encoded p)) :=
  fun p => (NBP_TransferEncode.result p).symm

theorem withdrawal_law : NBN_ValidatorSummary.NBN_Dep_WithdrawalEncode
    (fun p => ok (NBP_PaymentModel.withdrawal_encoded p)) :=
  fun p => (NBP_WithdrawalEncode.result p).symm

/-- Fully instantiated emitted validator composition; no inner codec premise. -/
theorem validator (s : NBN_StatementResult.Statement) :
    NBN_ValidatorSummary.run atomic_statement.encode_digest_canonical
      (fun p => ok (NBP_PaymentModel.transfer_encoded p))
      (fun p => ok (NBP_PaymentModel.withdrawal_encoded p)) s =
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s :=
  NBN_ValidatorSummary.source _ _ _ digest_canonical transfer_law withdrawal_law s

/-- Fully instantiated emitted encoder composition; exact bytes/error Result. -/
theorem encoder (s : NBN_StatementResult.Statement) :
    NBN_StatementEncoderSummary.run atomic_statement.encode_digest_canonical
      (fun p => ok (NBP_PaymentModel.transfer_encoded p))
      (fun p => ok (NBP_PaymentModel.withdrawal_encoded p)) s =
    NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s) :=
  NBN_StatementEncoderSummary.source _ _ _ digest_raw transfer_law withdrawal_law s

#print axioms digest_raw
#print axioms digest_canonical
#print axioms transfer_law
#print axioms withdrawal_law
#print axioms validator
#print axioms encoder
end NED_CodecComposition

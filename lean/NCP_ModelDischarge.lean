import NBP_DigestDecode
import NBP_TransferEncode
import NBP_WithdrawalEncode
import NBN_U05
set_option autoImplicit false
noncomputable section
namespace NCP_ModelDischarge
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K NBN_ValidatorSummary

/-- Model references only. Rust-reference extraction remains a separate obligation. -/
def digestRef : NBN_DigestResultDependency.Encode := fun d => ok (DigestBytes.bytes d)
def decodeRef : NBN_AfterDecodeTypes.Decode := fun b => ok (NBP_DigestDecode.decoded b)
def transferRef (p : Transfer) : PaymentResult := ok (NBP_PaymentModel.transfer_encoded p)
def withdrawalRef (p : Withdrawal) : PaymentResult := ok (NBP_PaymentModel.withdrawal_encoded p)

theorem digest_raw : NBN_DigestResultDependency.NBN_Dep_DigestEncodeRaw digestRef := by
  intro d
  rfl

theorem digest_source (d : NBN_DigestResultDependency.Digest) :
    digestRef d = atomic_statement.encode_digest_canonical d := (NBP_DigestEncode.result d).symm

theorem digest_canonical : NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical digestRef := by
  intro d _
  exact digest_raw d

theorem decode_source : NBN_AfterDecodeTypes.NBN_Dep_DigestDecode decodeRef := by
  intro b
  exact (NBP_DigestDecode.result b).symm

theorem transfer_source : NBN_Dep_TransferEncode transferRef := by
  intro p
  exact (NBP_TransferEncode.result p).symm

theorem withdrawal_source : NBN_Dep_WithdrawalEncode withdrawalRef := by
  intro p
  exact (NBP_WithdrawalEncode.result p).symm

theorem u03 :
    (∀ a, NBN_EncoderSummary.after digestRef a = pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 a) ∧
    (∀ s out, NBN_EncoderSummary.live digestRef s out = pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 s out) ∧
    (∀ s out, NBN_LateSummary.run digestRef s out = pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 s out) ∧
    (∀ bytes, NBN_AfterstateDecoderDependency.run decodeRef bytes = pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes) :=
  NBN_U03.conditional digestRef decodeRef digest_canonical decode_source

theorem u05 :
    (∀ s, NBN_ValidatorSummary.run digestRef transferRef withdrawalRef s =
      pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s) ∧
    (∀ s, NBN_StatementEncoderSummary.run digestRef transferRef withdrawalRef s =
      NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s)) :=
  NBN_U05.conditional digestRef transferRef withdrawalRef digest_raw transfer_source withdrawal_source

#print axioms digest_raw
#print axioms digest_source
#print axioms digest_canonical
#print axioms decode_source
#print axioms transfer_source
#print axioms withdrawal_source
#print axioms u03
#print axioms u05
end NCP_ModelDischarge

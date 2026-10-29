import NED_PaymentValidation
import NBP_CommonBytes
set_option autoImplicit false
noncomputable section
namespace NED_CommonEncodeCohort
open Aeneas Aeneas.Std Result NED_PaymentCohorts
abbrev TK := AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind
abbrev RK := AspisR1AdapterReconstruct.aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind

def toRawKind : TK → RK
  | .PrivateTransfer => .PrivateTransfer
  | .Withdrawal => .Withdrawal

/-- SAME arbitrary output prestate, magic, kind and common fields; this is
symbolic equality between emitted bodies, not a concrete buffer evaluation. -/
theorem source (out : Array U8 216#usize) (magic : Array U8 4#usize) (kind : TK) (c : C) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.encode_common
      out magic (toRawKind kind) (toRawCommon c) =
    AspisR1TerminalDecoder.pool_v1.payment_relation.encode_common out magic kind c := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.encode_common
    AspisR1TerminalDecoder.pool_v1.payment_relation.encode_common
  simp only [
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.POOL_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.NULLIFIER_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.ASSET_ID_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.NULLIFIER_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.ASSET_ID_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,
    AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION]
  cases kind <;> rfl

theorem result (out : Array U8 216#usize) (magic : Array U8 4#usize) (kind : TK) (c : C) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.encode_common
      out magic (toRawKind kind) (toRawCommon c) =
    ok (NBP_CommonBytes.encoded out magic kind c) := by
  rw [source,NBP_CommonBytes.result]

#print axioms source
#print axioms result
end NED_CommonEncodeCohort

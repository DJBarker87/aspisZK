import NDO_JHd_RequestNative
import NDO_JHb_S2K_StatementLane
import NDO_JFs_PublicValidation
set_option autoImplicit false
namespace AspisR1.JHd_RequestOperations
open Aeneas Aeneas.Std Result

/-- Native payment getter on the AdapterRw carrier. -/
def nullifier (payment : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1) :
    Result (Array U32 8#usize) :=
  match payment with
  | .PrivateTransfer p=>ok p.nullifier
  | .Withdrawal p=>ok p.nullifier

theorem nullifier_real : nullifier JHd_RequestCarrier.actual.«public»=ok JFt_Digest44.value := rfl
#print axioms nullifier_real

/-- The source helper has precisely one rejection kind. The native decoder
computes canonicality and the first encoded byte; it is not a fixture lookup. -/
def outputLane (digest : Array U32 8#usize) :
    Result (core.result.Result U8 AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) := do
  let result ← AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 digest
  match result with
  | .Err _=>ok (.Err .NonCanonicalDigest)
  | .Ok lane=>ok (.Ok lane)

theorem lane_real : outputLane JFt_Digest44.value=ok (.Ok 3#u8) := by
  have h:=S2K.StatementLane.lane JFs_PublicValue.value JFs_PublicValidation.source
  have native : AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
      JFt_Digest44.value=ok (.Ok 3#u8) := by
    simpa only [S2K.StatementChecks.nullifier,S2K.StatementAdmission.common,JFs_PublicValue.value,
      JFs_PublicValue.common,JFs_PaymentValue.value,JFs_PaymentValue.common] using h
  unfold outputLane
  rw [native,bind_tc_ok]
#print axioms lane_real
end AspisR1.JHd_RequestOperations

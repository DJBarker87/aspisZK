import NDO_JHg_RawCommon
import NDO_JHd_RequestNative
set_option autoImplicit false
namespace AspisR1.JHg_RawPrefix
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct r1_pool_adapter
open aspis_statement.pool_v1.pair_forest_terminal

def request := JHf_Carrier.toRequest JHd_RequestCarrier.actual

def payment : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  JHf_Carrier.toPoolV1PrivateTransferPublicV1
    (JHd_RequestCarrier.privateTransfer JHd_RequestPayment.value)

/-- The source reaches the terminal validator at the corrected expected record.
No successful authentication or terminal validator result is assumed here. -/
theorem source : reconstruct_asq8_statement request JHg_RawCommon.accounts JHg_RawCommon.candidate=
    transfer_statement_box JHg_RawCommon.common payment := by
  unfold reconstruct_asq8_statement
  have index : U64.checked_add JHg_RawCommon.accounts.live_snapshot.next_pair_index 1#u64=
      some JHg_RawCommon.candidate.next_pair_index := by rfl
  have compare : core.cmp.PartialEq.ne.trait_default
      (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64)
      (some JHg_RawCommon.candidate.next_pair_index)
      (some JHg_RawCommon.candidate.next_pair_index)=ok false := by rfl
  rw [index]
  simp only [lift,bind_tc_ok,compare,Bool.false_eq_true,ite_false]
  change (do
    let b ← core.cmp.PartialEq.ne.trait_default aspis_core.field.M31.Insts.CoreCmpPartialEqM31
      JHg_RawCommon.accounts.master.identity.asset_id payment.asset_id
    if b then ok (core.result.Result.Err solana_program_error.ProgramError.InvalidInstructionData :
      core.result.Result PoolV1PairForestTerminalStatementV1 solana_program_error.ProgramError) else do
      let c ← asq8_common JHg_RawCommon.accounts JHg_RawCommon.candidate
      transfer_statement_box c payment)=_
  have asset : core.cmp.PartialEq.ne.trait_default aspis_core.field.M31.Insts.CoreCmpPartialEqM31
      JHg_RawCommon.accounts.master.identity.asset_id payment.asset_id=ok false := by rfl
  rw [asset,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false,JHg_RawCommon.source,bind_tc_ok]
#print axioms source
end AspisR1.JHg_RawPrefix

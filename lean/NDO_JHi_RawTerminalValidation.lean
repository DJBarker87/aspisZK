import NDO_JHi_PaymentAccepted
import NDO_JHi_LateAccepted
import NDO_JHi_RawLane
import NDO_JHi_RawComparisons
set_option autoImplicit false
namespace AspisR1.JHi_RawTerminalValidation
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1.pair_forest_terminal

def value : PoolV1PairForestTerminalStatementV1 :=
  .PrivateTransfer JHg_RawCommon.common JHg_RawPrefix.payment

theorem source : validate_pool_v1_pair_forest_terminal_statement_v1 value=ok (.Ok ()) := by
  obtain ⟨encoded,payment⟩:=JHi_PaymentAccepted.source
  obtain ⟨updated,late,_⟩:=JHi_LateAccepted.source
    (Array.to_slice (Array.repeat 1520#usize 0#u8))
    (by simp only [Array.to_slice,Array.repeat,Slice.length,List.length_replicate];rfl)
  have common : PoolV1PairForestTerminalStatementV1.common value=ok JHg_RawCommon.common := rfl
  have publicCall : statement_public_common value=
      ok (JHg_RawPrefix.payment.pool,JHg_RawPrefix.payment.deployment_domain,
        JHg_RawPrefix.payment.anchor_sequence,JHg_RawPrefix.payment.anchor_root,
        JHg_RawPrefix.payment.nullifier,JHg_RawPrefix.payment.asset_id) := rfl
  have master : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      JHg_RawCommon.common.master_account (Array.repeat 32#usize 0#u8)=ok false :=
    JFs_PublicValue.master_nonzero
  have checkpoint : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      JHg_RawCommon.common.checkpoint_account (Array.repeat 32#usize 0#u8)=ok false :=
    JFs_PublicValue.checkpoint_nonzero
  have lane : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      JHg_RawCommon.common.selected_lane_account (Array.repeat 32#usize 0#u8)=ok false :=
    JFs_PublicValue.lane_nonzero
  have laneCall : aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
      JHg_RawPrefix.payment.nullifier=ok (.Ok 3#u8) := JHi_RawLane.source
  unfold validate_pool_v1_pair_forest_terminal_statement_v1
  rw [common]
  simp only [bind_tc_ok,master,checkpoint,lane,Bool.false_eq_true,↓reduceIte,
    lift,JHi_RawComparisons.lane_bound]
  rw [show value=.PrivateTransfer JHg_RawCommon.common JHg_RawPrefix.payment from rfl]
  simp only [payment,bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
  dsimp only [value] at publicCall
  rw [publicCall]
  simp only [uncurry,bind_tc_ok,JHi_RawComparisons.pool,JHi_RawComparisons.domain,
    JHi_RawComparisons.snapshot_pool,JHi_RawComparisons.anchor,JHi_RawComparisons.sequence,
    Bool.false_eq_true,↓reduceIte,laneCall,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,JHi_RawComparisons.lane]
  simp only [uncurry,Array.to_slice_mut,lift,bind_tc_ok]
  rw [late]
  simp only [uncurry,bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
#print axioms source
end AspisR1.JHi_RawTerminalValidation

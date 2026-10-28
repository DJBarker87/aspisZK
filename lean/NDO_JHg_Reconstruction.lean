import NDO_JHg_RawPrefix
import NDO_JHf_ReconstructionSlot
set_option autoImplicit false
namespace AspisR1.JHg_Reconstruction
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct r1_pool_adapter
open aspis_statement.pool_v1.pair_forest_terminal

theorem target : PoolV1PairForestTerminalStatementV1.PrivateTransfer
    JHg_RawCommon.common JHg_RawPrefix.payment=
    JHf_Carrier.toPoolV1PairForestTerminalStatementV1 JGx_RealStatement.value := rfl
#print axioms target

/-- Actual extracted reconstruction reduces to precisely this remaining native
validator call. The validator observation is explicit and not yet discharged. -/
theorem source
    (validated : validate_pool_v1_pair_forest_terminal_statement_v1
      (.PrivateTransfer JHg_RawCommon.common JHg_RawPrefix.payment)=ok (.Ok ())) :
    JHf_ReconstructionSlot.source JHd_RequestCarrier.actual JHg_AccountValues.value
      JHd_ScanValue.candidate=ok (.Ok JGx_RealStatement.value) := by
  have raw : reconstruct_asq8_statement JHg_RawPrefix.request JHg_RawCommon.accounts
      JHg_RawCommon.candidate=ok (.Ok
        (JHf_Carrier.toPoolV1PairForestTerminalStatementV1 JGx_RealStatement.value)) := by
    rw [JHg_RawPrefix.source]
    unfold transfer_statement_box
    rw [validated]
    simp only [bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
    rw [target]
  dsimp only [JHg_RawPrefix.request,JHg_RawCommon.accounts,JHg_RawCommon.candidate] at raw
  unfold JHf_ReconstructionSlot.source
  rw [raw,bind_tc_ok]
  simp only [JHf_Carrier.from_toPoolV1PairForestTerminalStatementV1]
#print axioms source
end AspisR1.JHg_Reconstruction

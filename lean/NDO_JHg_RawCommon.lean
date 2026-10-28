import NDO_JHg_AccountValues
import ExtractedAdapterReconstructSuccess
import NDO_JHf_ExactDomainObstruction
set_option autoImplicit false
namespace AspisR1.JHg_RawCommon
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct r1_pool_adapter
open aspis_statement.pool_v1.pair_forest_terminal

def accounts := JHf_Carrier.toAuthenticatedAsq8Accounts JHg_AccountValues.value
def candidate := JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 JHd_ScanValue.candidate
def common : PoolV1PairForestTerminalCommonV1 :=
  match JHf_Carrier.toPoolV1PairForestTerminalStatementV1 JGx_RealStatement.value with
  | .PrivateTransfer c _=>c
  | .Withdrawal c _=>c

theorem source : asq8_common accounts candidate=ok common := by
  rw [AdapterReconstructSuccess.asq8_common_exact]
  unfold AdapterReconstructSuccess.common accounts JHg_AccountValues.value
    JHg_AccountValues.live JHg_AccountValues.lane JHg_AccountValues.master
    JHg_AccountValues.checkpoint
  simp only [JHg_Scalar09.native,JHg_Scalar18.native,JHg_AccountValues.domain_target]
  rfl
#print axioms source
end AspisR1.JHg_RawCommon

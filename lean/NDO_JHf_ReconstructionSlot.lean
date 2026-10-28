import JHf_ProgramErrorCarrier
import NDO_JHf_NoReconstruction
set_option autoImplicit false
namespace AspisR1.JHf_ReconstructionSlot
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

def source (request : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1)
    (accounts : r1_pool_adapter.AuthenticatedAsq8Accounts)
    (candidate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
    Result (core.result.Result
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
      solana_program_error.ProgramError) := do
  let result ← AspisR1AdapterReconstruct.r1_pool_adapter.reconstruct_asq8_statement
    (JHf_Carrier.toRequest request) (JHf_Carrier.toAuthenticatedAsq8Accounts accounts)
    (JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 candidate)
  match result with
  | .Ok statement=>ok (.Ok (JHf_Carrier.fromPoolV1PairForestTerminalStatementV1 statement))
  | .Err error=>ok (.Err (JHf_ProgramErrorCarrier.fromRaw error))

theorem no_success (accounts : r1_pool_adapter.AuthenticatedAsq8Accounts)
    (candidate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (faithful : accounts.live_snapshot.deployment_domain=JHf_DomainBytes.master) :
    ¬∃ out,source JHd_RequestCarrier.actual accounts candidate=ok (.Ok out) := by
  rintro ⟨out,run⟩
  unfold source at run
  have impossible:=JHf_NoReconstruction.source (JHf_Carrier.toAuthenticatedAsq8Accounts accounts)
    (JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 candidate) faithful
  change ¬∃ out,AspisR1AdapterReconstruct.r1_pool_adapter.reconstruct_asq8_statement
    (JHf_Carrier.toRequest JHd_RequestCarrier.actual) (JHf_Carrier.toAuthenticatedAsq8Accounts accounts)
    (JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 candidate)=ok (.Ok out) at impossible
  cases call : AspisR1AdapterReconstruct.r1_pool_adapter.reconstruct_asq8_statement
      (JHf_Carrier.toRequest JHd_RequestCarrier.actual) (JHf_Carrier.toAuthenticatedAsq8Accounts accounts)
      (JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 candidate) with
  | fail e=>simp only [call,bind_tc_fail] at run;cases run
  | div=>simp only [call,bind_tc_div] at run;cases run
  | ok result=>
    cases result with
    | Err e=>simp only [call,bind_tc_ok] at run;cases run
    | Ok value=>exact impossible ⟨value,call⟩
#print axioms no_success
end AspisR1.JHf_ReconstructionSlot

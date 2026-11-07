import NNH_MRegistryV2GuardFactor
import NNH_MEntry2ValueRSL
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry2Program
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
def run (ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let s3 ←
    ops.op40
      registry_program
  let s4 ←
    lift (Array.to_slice
      (Array.make 1#usize [ val1.programdata_bump ]))
  let s5 ←
    lift (Array.to_slice
      (Array.make 2#usize [ s3, s4 ]))
  let r8 ←
    ops.op38 s5
      loader
  let r9 ←
    AdapterRw.core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_3.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
      r8 ()
  let cf5 ←
    core.result.Result.Insts.CoreOpsTry.branch r9
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue val3 =>
    NNH_MRegistry2Guard.run ops verifier_program p registry_program loader master entry_account current_slot val1 val3
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      solana_program_error.ProgramError) residual

end NNH_MRegistry2Program
end

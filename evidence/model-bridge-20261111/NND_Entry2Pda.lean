import NND_RegistryV2ExpectedFactor
import NND_Entry2ValueRSL
set_option autoImplicit false
noncomputable section
namespace NND_Entry2Pda
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
def run (ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize)
 (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let s6 ←
    ops.op40
      p
  let s7 ←
    lift (Array.to_slice
      r1_pool_adapter.PROFILE_BINDING)
  let s8 ←
    lift (Array.to_slice
      r1_pool_adapter.RELEASE_BINDING)
  let s9 ←
    lift (Array.to_slice
      (Array.make 1#usize [
        val5.bump
        ]))
  let s10 ←
    lift (Array.to_slice
      (Array.make 5#usize [
        r1_pool_adapter.VERIFIER_ENTRY_V2_SEED,
        s6, s7, s8, s9
        ]))
  let r14 ←
    ops.op38
      s10 registry_program
  let r15 ←
    AdapterRw.core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_5.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
      r14 ()
  let cf9 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r15
  match cf9 with
  |
    core.ops.control_flow.ControlFlow.Continue
    val6 =>
    NND_Entry2Expected.run ops verifier_program p loader entry_account current_slot a6 val5 val6
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit
      (core.convert.FromSame
      solana_program_error.ProgramError)
      residual

end NND_Entry2Pda
end

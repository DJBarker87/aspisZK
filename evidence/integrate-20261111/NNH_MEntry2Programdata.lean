import NNH_MRegistryV2EntryFactor
import NNH_MEntry2ValueRSL
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry2Programdata
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
def run (ops : Ops) (verifier_program p loader : solana_pubkey.Pubkey)
 (current_slot : U64) (a6 : Array U8 32#usize)
 (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let s11 ←
    ops.op40
      verifier_program
  let s12 ←
    lift (Array.to_slice
      (Array.make 1#usize [
        val5.programdata_bump
        ]))
  let s13 ←
    lift (Array.to_slice
      (Array.make 2#usize [
        s11, s12
        ]))
  let r16 ←
    ops.op38
      s13 loader
  let r17 ←
    AdapterRw.core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_6.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
      r16 ()
  let cf10 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r17
  match cf10 with
  |
    core.ops.control_flow.ControlFlow.Continue
    val7 =>
    NNH_MRegistryEntry2Check.check ops verifier_program p current_slot a6 val5 val7
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit
      (core.convert.FromSame
      solana_program_error.ProgramError)
      residual

end NNH_MEntry2Programdata
end

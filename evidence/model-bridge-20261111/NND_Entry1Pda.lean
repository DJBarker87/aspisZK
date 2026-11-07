import NND_RegistryEntry1Value
import NND_PdaTransport
set_option autoImplicit false
noncomputable section
namespace NND_Entry1Pda
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
def run (ops : Ops) (verifier_program p registry_program : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val4 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let s3 ←
    ops.op40
      p
  let s4 ←
    lift (Array.to_slice
      r1_pool_adapter.PROFILE_BINDING)
  let s5 ←
    lift (Array.to_slice
      r1_pool_adapter.RELEASE_BINDING)
  let s6 ←
    lift (Array.to_slice
      (Array.make 1#usize [
        val4.bump
        ]))
  let s7 ←
    lift (Array.to_slice
      (Array.make 5#usize [
        r1_pool_adapter.VERIFIER_ENTRY_SEED,
        s3, s4, s5, s6
        ]))
  let r12 ←
    ops.op38
      s7 registry_program
  let r13 ←
    AdapterRw.core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_10.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
      r12 ()
  let cf8 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r13
  match cf8 with
  |
    core.ops.control_flow.ControlFlow.Continue
    val5 =>
    NND_RegistryEntry1Check.check ops verifier_program p entry_account current_slot val4 val5
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      solana_program_error.ProgramError)
      residual

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p rp : solana_pubkey.Pubkey) (e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) :
 run (NND_RegistryOps.install base D env) v p rp e t entry =
 NND_FormatControl.thenCall (NND_RegistryOps.pda env (NND_PdaSeeds.entry1 p entry.bump) rp)
  (NND_RegistryEntry1Check.check (NND_RegistryOps.install base D env) v p e t entry) := by
 unfold run
 simp only [NND_RegistryScalarOps.as_ref,bind_tc_ok,lift]
 change _ = NND_FormatControl.thenCall ((NND_RegistryOps.install base D env).op38 (NND_PdaSeeds.entry1 p entry.bump) rp) _
 change _ = NND_FormatControl.thenCall (NND_RegistryOps.pda env (NND_PdaSeeds.entry1 p entry.bump) rp) _
 unfold NND_FormatControl.thenCall
 unfold NND_PdaSeeds.entry1 NND_PdaSeeds.one
 cases h : env.pda ((NND_PdaSeeds.entry1 p entry.bump).val.map bytes) (key rp) <;>
  (simp only [NND_RegistryOps.install,NND_RegistryOps.pda,NND_PdaSeeds.entry1,NND_PdaSeeds.one] at h ⊢
   simp only [h,bind_tc_ok]
   rfl)


#print axioms source
end NND_Entry1Pda
end

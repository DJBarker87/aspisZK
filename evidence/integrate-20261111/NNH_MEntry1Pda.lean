import NNH_MRegistryEntry1Value
import NNH_MPdaTransport
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry1Pda
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
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
    NNH_MRegistryEntry1Check.check ops verifier_program p entry_account current_slot val4 val5
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
 run (NNH_MRegistryOps.install base D env) v p rp e t entry =
 NNH_MFormatControl.thenCall (NNH_MRegistryOps.pda env (NNH_MPdaSeeds.entry1 p entry.bump) rp)
  (NNH_MRegistryEntry1Check.check (NNH_MRegistryOps.install base D env) v p e t entry) := by
 unfold run
 simp only [NNH_MRegistryScalarOps.as_ref,bind_tc_ok,lift]
 change _ = NNH_MFormatControl.thenCall ((NNH_MRegistryOps.install base D env).op38 (NNH_MPdaSeeds.entry1 p entry.bump) rp) _
 change _ = NNH_MFormatControl.thenCall (NNH_MRegistryOps.pda env (NNH_MPdaSeeds.entry1 p entry.bump) rp) _
 unfold NNH_MFormatControl.thenCall
 unfold NNH_MPdaSeeds.entry1 NNH_MPdaSeeds.one
 cases h : env.pda ((NNH_MPdaSeeds.entry1 p entry.bump).val.map bytes) (key rp) <;>
  (simp only [NNH_MRegistryOps.install,NNH_MRegistryOps.pda,NNH_MPdaSeeds.entry1,NNH_MPdaSeeds.one] at h ⊢
   simp only [h,bind_tc_ok]
   rfl)


#print axioms source
end NNH_MEntry1Pda
end

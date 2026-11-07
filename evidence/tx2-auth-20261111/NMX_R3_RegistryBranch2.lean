import NMX_R3_RegistryFold3
import NMX_R3_RegistryDataLaw
import NMX_R3_RegistryProtocols
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryBranch2
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
abbrev Output := core.result.Result Unit solana_program_error.ProgramError

def program (ops : Ops) (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) (loader rp : solana_pubkey.Pubkey) : Program Output := do
 let r ← data reg
 NMX_R3_RegistryProtocols.tryTail r (fun b => NMX_R3_RegistryScriptParts.script003 ops v m s reg ent t loader rp b)

theorem source (ops : Ops) (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) (loader rp : solana_pubkey.Pubkey) :
 eval (program ops v m s reg ent t loader rp) = RSL.Spec.bind (dataSpec reg)
  (NMX_R3_RegistryDataLaw.next (fun b => eval (NMX_R3_RegistryScriptParts.script003 ops v m s reg ent t loader rp b))) := by
 simp only [program,eval_bind,eval_data]
 apply congrArg (RSL.Spec.bind (dataSpec reg))
 funext r
 cases r with
 | Ok b => exact NMX_R3_RegistryProtocols.eval_try (.Ok b) (fun b => NMX_R3_RegistryScriptParts.script003 ops v m s reg ent t loader rp b)
 | Err e => exact NMX_R3_RegistryProtocols.eval_try (.Err e) (fun b => NMX_R3_RegistryScriptParts.script003 ops v m s reg ent t loader rp b)

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 RSL.Spec.map (reply id) (eval (program (NMX_R3_RegistryOps.install base D env) v m s reg ent t (unkey RSL.LOADER_ID) (unkey D.registry))) =
 RSL.TX2_234.immutableBranch LIBB_PoolLib.library D (NMX_R3_RegistryArgs.args v p m s reg ent t) := by
 rw [source]
 apply (NMX_R3_RegistryDataLaw.fold reg _
  (NMX_R3_RegistryFold3.tail D (NMX_R3_RegistryArgs.args v p m s reg ent t))
  (fun b => NMX_R3_RegistryFold3.fold base D env v p m s reg ent t b)).trans
 rfl
#print axioms source
#print axioms fold
end NMX_R3_RegistryBranch2
end

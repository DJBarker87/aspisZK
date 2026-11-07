import NMX_R3_RegistryBranch1
import NMX_R3_RegistryBranch2
import NMX_R3_RegistryPure
import NND_ScalarComparison
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryBranches
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp : solana_pubkey.Pubkey) :
 eval (NMX_R3_RegistryScriptParts.script002 (NMX_R3_RegistryOps.install base D env) v m s reg ent t rp) =
 (if s.verifier_policy.flags &&& 2#u8 != 0#u8 then
  eval (NMX_R3_RegistryBranch2.program (NMX_R3_RegistryOps.install base D env) v m s reg ent t (unkey RSL.LOADER_ID) rp)
 else eval (NMX_R3_RegistryBranch1.program (NMX_R3_RegistryOps.install base D env) v m s reg ent t rp)) := by
 simp only [NMX_R3_RegistryScriptParts.script002,NMX_R3_RegistryBranch1.program,
  NMX_R3_RegistryBranch2.program,NMX_R3_RegistryProtocols.tryTail,eval_bind,eval_scalar,
  eval_if,NMX_R3_RegistryScalarOps.deployment_flag,NMX_R3_RegistryScalarOps.loader,
  Aeneas.Std.lift,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure]

def reference (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) : RSL.RS Unit :=
 if a.master.verifier_policy.flags &&& RSL.POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0 then
  RSL.TX2_234.immutableBranch LIBB_PoolLib.library D a
 else RSL.TX2_234.v1Branch LIBB_PoolLib.library D a

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script002 (NMX_R3_RegistryOps.install base D env) v m s reg ent t (unkey D.registry))) =
 reference D (NMX_R3_RegistryArgs.args v p m s reg ent t) := by
 rw [source]
 unfold reference
 change _ = if byte s.verifier_policy.flags &&& RSL.POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0 then _ else _
 rw [NND_Carrier.flags]
 simp only [show byte 2#u8 = (2 : UInt8) from rfl,RSL.POLICY_FLAG_IMMUTABLE_DEPLOYMENT]
 by_cases flag : (byte s.verifier_policy.flags &&& 2 != (0 : UInt8)) = true
 · simp only [flag,if_true]
   exact NMX_R3_RegistryBranch2.fold base D env v p m s reg ent t
 · simp only [flag,if_false]
   exact NMX_R3_RegistryBranch1.fold base D env v p m s reg ent t

#print axioms source
#print axioms fold
end NMX_R3_RegistryBranches
end

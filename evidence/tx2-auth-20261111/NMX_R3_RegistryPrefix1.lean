import NMX_R3_RegistryBranches
import NMX_R3_RegistryReadonly
import NMX_R3_RegistryPure
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPrefix1
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp : solana_pubkey.Pubkey) :
 eval (NMX_R3_RegistryScriptParts.script001 (NMX_R3_RegistryOps.install base D env) v m s reg ent t rp) =
 eval (NMX_R3_RegistryReadonly.call (NMX_R3_RegistryOps.install base D env) reg rp
  (NMX_R3_RegistryScriptParts.script002 (NMX_R3_RegistryOps.install base D env) v m s reg ent t rp)) := by
 simp only [NMX_R3_RegistryScriptParts.script001,NMX_R3_RegistryReadonly.call,
  NMX_R3_RegistryProtocols.tryTail,eval_bind,eval_scalar,
  NMX_R3_RegistryScalarOps.from_bytes,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure]

def reference (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) : RSL.RS Unit :=
 RSL.RS.seq (RSL.RS.ofExcept (RSL.readonlyAccount a.registry_account D.registry))
  (NMX_R3_RegistryBranches.reference D a)

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script001 (NMX_R3_RegistryOps.install base D env) v m s reg ent t (unkey D.registry))) =
 reference D (NMX_R3_RegistryArgs.args v p m s reg ent t) := by
 rw [source]
 have h := NMX_R3_RegistryReadonly.fold base D env reg (unkey D.registry)
  (NMX_R3_RegistryScriptParts.script002 (NMX_R3_RegistryOps.install base D env) v m s reg ent t (unkey D.registry))
  (NMX_R3_RegistryBranches.reference D (NMX_R3_RegistryArgs.args v p m s reg ent t))
  (NMX_R3_RegistryBranches.fold base D env v p m s reg ent t)
 rw [key_forth] at h
 exact h
#print axioms source
#print axioms fold
end NMX_R3_RegistryPrefix1
end

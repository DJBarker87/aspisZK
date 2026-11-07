import NMX_R3_RegistryFold16
import NMX_R3_RegistryData015
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryFold15
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects

def tail (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) : RSL.RS Unit :=
 RSL.RS.bind a.entry_account.data (NMX_R3_RegistryFold16.tail D a)

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script015 (NMX_R3_RegistryOps.install base D env)
   v ent t m.key (unkey D.registry))) =
 tail D (NMX_R3_RegistryArgs.args v p m s reg ent t) := by
 rw [NMX_R3_RegistryData015.source]
 exact NMX_R3_RegistryDataLaw.fold ent _
  (NMX_R3_RegistryFold16.tail D (NMX_R3_RegistryArgs.args v p m s reg ent t))
  (fun b => NMX_R3_RegistryFold16.fold base D env v p m s reg ent t b)
#print axioms fold
end NMX_R3_RegistryFold15
end

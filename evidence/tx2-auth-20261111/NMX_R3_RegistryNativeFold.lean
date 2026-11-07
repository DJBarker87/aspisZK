import NMX_R3_RegistryTop
import NMX_R3_RegistrySource
import NMX_R3_RegistryObserve
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryNativeFold
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects

def execution (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) (allocations : Nat → Bool)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) : RSL.Obs (Except RSL.ProgramError Unit) :=
 NMX_R3_RegistryObserve.map (reply id)
  (NMX_R3_RegistryRun.run env allocations
   (NMX_R3_RegistryScriptParts.script000 (NMX_R3_RegistryOps.install base D env) v p m s reg ent t) 0)

/-- Complete observation refinement at every original typed input and every
allocation stream. The separate source factor identifies all132 call sites. -/
theorem native (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) (allocations : Nat → Bool)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 RSL.TX2_234.Ref LIBB_PoolLib.library D (NMX_R3_RegistryArgs.args v p m s reg ent t) env
  (execution base D env allocations v p m s reg ent t) := by
 have h := NMX_R3_RegistryObserve.sound (reply id)
  (eval (NMX_R3_RegistryScriptParts.script000 (NMX_R3_RegistryOps.install base D env) v p m s reg ent t)) env _
  (NMX_R3_RegistryRun.sound env allocations _ 0)
 rw [NMX_R3_RegistryTop.fold] at h
 exact h
#print axioms native
end NMX_R3_RegistryNativeFold
end

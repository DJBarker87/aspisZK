import NND_Registry2Expected
import NND_Registry2ProgramValue
set_option autoImplicit false
noncomputable section
namespace NND_Registry2ExpectedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV2) (expected : RSL.B32) : Except RSL.ProgramError Unit :=
 eseq (echeck (decide (a.registry_account.key ≠ expected)) .invalidAccountData)
 (NND_Registry2ProgramValue.tail L D a env reg)

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2)
 (expected : solana_pubkey.Pubkey) :
 outer (reply id) (NND_Registry2Expected.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s r e t reg expected) =
 ok (tail L D (NND_RegistryArgs.args v p m s r e t) env (registryV2 reg) (key expected)) := by
 unfold NND_Registry2Expected.run tail
 simp only [r1_pool_adapter.owned.OwnedAccount.impl.key,NND_RegistryStd.key_ne,bind_tc_ok,NND_CompareTransport.key_ne]
 rw [show (NND_RegistryArgs.args v p m s r e t).registry_account.key = key r.key from rfl]
 cases hk : decide (key r.key ≠ key expected)
 · exact NND_Registry2ProgramValue.value base L D env v p m s r e t reg
 · rfl

#print axioms value
end NND_Registry2ExpectedValue
end

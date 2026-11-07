import NNH_MRegistry2Expected
import NNH_MRegistry2ProgramValue
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry2ExpectedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV2) (expected : RSL.B32) : Except RSL.ProgramError Unit :=
 eseq (echeck (decide (a.registry_account.key ≠ expected)) .invalidAccountData)
 (NNH_MRegistry2ProgramValue.tail L D a env reg)

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2)
 (expected : solana_pubkey.Pubkey) :
 outer (reply id) (NNH_MRegistry2Expected.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s r e t reg expected) =
 ok (tail L D (NNH_MRegistryArgs.args v p m s r e t) env (registryV2 reg) (key expected)) := by
 unfold NNH_MRegistry2Expected.run tail
 simp only [r1_pool_adapter.owned.OwnedAccount.impl.key,NNH_MRegistryStd.key_ne,bind_tc_ok,NND_CompareTransport.key_ne]
 rw [show (NNH_MRegistryArgs.args v p m s r e t).registry_account.key = key r.key from rfl]
 cases hk : decide (key r.key ≠ key expected)
 · exact NNH_MRegistry2ProgramValue.value base L D env v p m s r e t reg
 · rfl

#print axioms value
end NNH_MRegistry2ExpectedValue
end

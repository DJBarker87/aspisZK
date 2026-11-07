import NNH_MEntry2Expected
import NNH_MEntry2ProgramdataValue
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry2ExpectedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

def tail (env : RSL.Env) (a : RSL.TX2_234.Args) (entry : RSL.EntryV2) (expected : RSL.B32) : Except RSL.ProgramError Unit :=
 eseq (echeck (decide (a.entry_account.key ≠ expected)) .invalidAccountData)
 (NNH_MEntry2ProgramdataValue.tail env a entry)

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2)
 (expected : solana_pubkey.Pubkey) :
 outer (reply id) (NNH_MEntry2Expected.run (NNH_MRegistryOps.install base D env) v m.key (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID) entry expected) =
 ok (tail env (NNH_MRegistryArgs.args v p m s r e t) (entryV2 entry) (key expected)) := by
 unfold NNH_MEntry2Expected.run tail
 simp only [r1_pool_adapter.owned.OwnedAccount.impl.key,NNH_MRegistryStd.key_ne,bind_tc_ok,NND_CompareTransport.key_ne]
 rw [show (NNH_MRegistryArgs.args v p m s r e t).entry_account.key = key e.key from rfl]
 cases hk : decide (key e.key ≠ key expected)
 · exact NNH_MEntry2ProgramdataValue.value base D env v p m s r e t entry
 · rfl

#print axioms value
end NNH_MEntry2ExpectedValue
end

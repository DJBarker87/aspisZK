import NND_Entry2Expected
import NND_Entry2ProgramdataValue
set_option autoImplicit false
noncomputable section
namespace NND_Entry2ExpectedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

def tail (env : RSL.Env) (a : RSL.TX2_234.Args) (entry : RSL.EntryV2) (expected : RSL.B32) : Except RSL.ProgramError Unit :=
 eseq (echeck (decide (a.entry_account.key ≠ expected)) .invalidAccountData)
 (NND_Entry2ProgramdataValue.tail env a entry)

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2)
 (expected : solana_pubkey.Pubkey) :
 outer (reply id) (NND_Entry2Expected.run (NND_RegistryOps.install base D env) v m.key (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID) entry expected) =
 ok (tail env (NND_RegistryArgs.args v p m s r e t) (entryV2 entry) (key expected)) := by
 unfold NND_Entry2Expected.run tail
 simp only [r1_pool_adapter.owned.OwnedAccount.impl.key,NND_RegistryStd.key_ne,bind_tc_ok,NND_CompareTransport.key_ne]
 rw [show (NND_RegistryArgs.args v p m s r e t).entry_account.key = key e.key from rfl]
 cases hk : decide (key e.key ≠ key expected)
 · exact NND_Entry2ProgramdataValue.value base D env v p m s r e t entry
 · rfl

#print axioms value
end NND_Entry2ExpectedValue
end

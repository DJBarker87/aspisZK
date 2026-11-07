import NND_RegistryEntry1Value
import NND_ReplyForth
set_option autoImplicit false
noncomputable section
namespace NND_Entry1ValueRSL
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1)
 (expected : solana_pubkey.Pubkey) :
 outer (reply id) (NND_RegistryEntry1Check.check (NND_RegistryOps.install base D env) v m.key e t entry expected) =
 ok (eseq (echeck (decide ((account e).key ≠ key expected)) .invalidAccountData)
  (eseq (echeck (RSL.TX2_234.entryV1Bad (NND_RegistryArgs.args v p m s r e t) (entryV1 entry)) .invalidAccountData) (.ok ()))) := by
 rw [NND_RegistryEntry1Value.value,NND_CompareTransport.key_ne,NND_EntryRecordGuards.entry1 v p m s r e t]
 change outer (reply id) (ok (if decide ((account e).key ≠ key expected) || _ then _ else _)) = _
 cases h : decide ((account e).key ≠ key expected) <;>
 cases hb : RSL.TX2_234.entryV1Bad (NND_RegistryArgs.args v p m s r e t) (entryV1 entry) <;> rfl

#print axioms value
end NND_Entry1ValueRSL
end

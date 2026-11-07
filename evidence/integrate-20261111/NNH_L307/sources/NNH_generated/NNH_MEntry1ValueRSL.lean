import NNH_MRegistryEntry1Value
import NND_ReplyForth
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry1ValueRSL
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1)
 (expected : solana_pubkey.Pubkey) :
 outer (reply id) (NNH_MRegistryEntry1Check.check (NNH_MRegistryOps.install base D env) v m.key e t entry expected) =
 ok (eseq (echeck (decide ((account e).key ≠ key expected)) .invalidAccountData)
  (eseq (echeck (RSL.TX2_234.entryV1Bad (NNH_MRegistryArgs.args v p m s r e t) (entryV1 entry)) .invalidAccountData) (.ok ()))) := by
 rw [NNH_MRegistryEntry1Value.value,NND_CompareTransport.key_ne,NNH_MEntryRecordGuards.entry1 v p m s r e t]
 change outer (reply id) (ok (if decide ((account e).key ≠ key expected) || _ then _ else _)) = _
 cases h : decide ((account e).key ≠ key expected) <;>
 cases hb : RSL.TX2_234.entryV1Bad (NNH_MRegistryArgs.args v p m s r e t) (entryV1 entry) <;> rfl

#print axioms value
end NNH_MEntry1ValueRSL
end

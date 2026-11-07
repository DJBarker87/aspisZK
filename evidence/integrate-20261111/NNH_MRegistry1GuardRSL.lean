import NNH_MRegistry1GuardValue
import NNH_MEntry1ReadonlyValue
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry1GuardRSL
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV1) (expected : RSL.B32) : Except RSL.ProgramError Unit :=
 eseq (echeck (decide (a.registry_account.key ≠ expected)) .invalidAccountData)
 (eseq (echeck (RSL.TX2_234.registryV1Bad a reg) .invalidAccountData)
 (eseq (RSL.readonlyAccount a.entry_account D.registry)
 (ebind a.entry_account.bytes (fun b =>
  ebind (option ((NNH_MRegistryLibrary.install L).decodeEntryV1 b) .invalidAccountData)
   (NNH_MEntry1DecodedValue.tail env D a)))))

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1)
 (expected : solana_pubkey.Pubkey) :
 outer (reply id) (NNH_MRegistry1Guard.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) s r e t reg expected) =
 ok (tail L D (NNH_MRegistryArgs.args v p m s r e t) env (registryV1 reg) (key expected)) := by
 rw [NNH_MRegistry1GuardValue.value,NND_CompareTransport.key_ne,NNH_MRegistryRecordGuards.registry1 v p m s r e t]
 unfold tail
 rw [show (NNH_MRegistryArgs.args v p m s r e t).registry_account.key = key r.key from rfl]
 cases hk : decide (key r.key ≠ key expected) <;>
 cases hb : RSL.TX2_234.registryV1Bad (NNH_MRegistryArgs.args v p m s r e t) (registryV1 reg)
 · exact NNH_MEntry1ReadonlyValue.value base L D env v p m s r e t
 · rfl
 · rfl
 · rfl

#print axioms value
end NNH_MRegistry1GuardRSL
end

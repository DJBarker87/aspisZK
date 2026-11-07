import NND_Registry1GuardValue
import NND_Entry1ReadonlyValue
set_option autoImplicit false
noncomputable section
namespace NND_Registry1GuardRSL
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV1) (expected : RSL.B32) : Except RSL.ProgramError Unit :=
 eseq (echeck (decide (a.registry_account.key ≠ expected)) .invalidAccountData)
 (eseq (echeck (RSL.TX2_234.registryV1Bad a reg) .invalidAccountData)
 (eseq (RSL.readonlyAccount a.entry_account D.registry)
 (ebind a.entry_account.data (fun b =>
  ebind (option ((NND_RegistryLibrary.install L).decodeEntryV1 b) .invalidAccountData)
   (NND_Entry1DecodedValue.tail env D a)))))

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1)
 (expected : solana_pubkey.Pubkey) :
 outer (reply id) (NND_Registry1Guard.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) s r e t reg expected) =
 ok (tail L D (NND_RegistryArgs.args v p m s r e t) env (registryV1 reg) (key expected)) := by
 rw [NND_Registry1GuardValue.value,NND_CompareTransport.key_ne,NND_RegistryRecordGuards.registry1 v p m s r e t]
 unfold tail
 rw [show (NND_RegistryArgs.args v p m s r e t).registry_account.key = key r.key from rfl]
 cases hk : decide (key r.key ≠ key expected) <;>
 cases hb : RSL.TX2_234.registryV1Bad (NND_RegistryArgs.args v p m s r e t) (registryV1 reg)
 · exact NND_Entry1ReadonlyValue.value base L D env v p m s r e t
 · rfl
 · rfl
 · rfl

#print axioms value
end NND_Registry1GuardRSL
end

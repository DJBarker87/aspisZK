import NND_Registry2GuardValue
import NND_Entry2ReadonlyValue
set_option autoImplicit false
noncomputable section
namespace NND_Registry2GuardRSL
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV2) (rpd : RSL.B32) : Except RSL.ProgramError Unit :=
 eseq (echeck (RSL.TX2_234.registryV2Bad D a reg rpd) .invalidAccountData)
 (eseq (RSL.readonlyAccount a.entry_account D.registry)
 (ebind a.entry_account.data (fun b =>
  ebind (option ((NND_RegistryLibrary.install L).decodeEntryV2 b) .invalidAccountData)
   (NND_Entry2PdaValue.tail env D a))))

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2)
 (rpd : solana_pubkey.Pubkey) :
 outer (reply id) (NND_Registry2Guard.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s e t reg rpd) =
 ok (tail L D (NND_RegistryArgs.args v p m s r e t) env (registryV2 reg) (key rpd)) := by
 rw [NND_Registry2GuardValue.value,NND_RegistryRecordGuards.registry2 D v p m s r e t]
 unfold tail
 cases hb : RSL.TX2_234.registryV2Bad D (NND_RegistryArgs.args v p m s r e t) (registryV2 reg) (key rpd)
 · exact NND_Entry2ReadonlyValue.value base L D env v p m s r e t
 · rfl

#print axioms value
end NND_Registry2GuardRSL
end

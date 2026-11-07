import NNH_MRegistry2GuardValue
import NNH_MEntry2ReadonlyValue
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry2GuardRSL
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV2) (rpd : RSL.B32) : Except RSL.ProgramError Unit :=
 eseq (echeck (RSL.TX2_234.registryV2Bad D a reg rpd) .invalidAccountData)
 (eseq (RSL.readonlyAccount a.entry_account D.registry)
 (ebind a.entry_account.bytes (fun b =>
  ebind (option ((NNH_MRegistryLibrary.install L).decodeEntryV2 b) .invalidAccountData)
   (NNH_MEntry2PdaValue.tail env D a))))

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2)
 (rpd : solana_pubkey.Pubkey) :
 outer (reply id) (NNH_MRegistry2Guard.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s e t reg rpd) =
 ok (tail L D (NNH_MRegistryArgs.args v p m s r e t) env (registryV2 reg) (key rpd)) := by
 rw [NNH_MRegistry2GuardValue.value,NNH_MRegistryRecordGuards.registry2 D v p m s r e t]
 unfold tail
 cases hb : RSL.TX2_234.registryV2Bad D (NNH_MRegistryArgs.args v p m s r e t) (registryV2 reg) (key rpd)
 · exact NNH_MEntry2ReadonlyValue.value base L D env v p m s r e t
 · rfl

#print axioms value
end NNH_MRegistry2GuardRSL
end

import NND_Entry1DecodeTransport
set_option autoImplicit false
noncomputable section
namespace NND_Entry1DecodedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

def tail (env : RSL.Env) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (entry : RSL.EntryV1) : Except RSL.ProgramError Unit :=
 ebind (option (env.pda [RSL.SEED_ENTRY,a.master_account.key.bytes,RSL.PROFILE_BINDING.bytes,RSL.RELEASE_BINDING.bytes,[entry.bump]] D.registry) .invalidAccountData) fun expected =>
  eseq (echeck (decide (a.entry_account.key ≠ expected)) .invalidAccountData)
   (eseq (echeck (RSL.TX2_234.entryV1Bad a entry) .invalidAccountData) (.ok ()))

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id) (NND_Entry1Decode.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) e t) =
 ok (ebind (account e).data (fun b =>
  ebind (option ((NND_RegistryLibrary.install L).decodeEntryV1 b) .invalidAccountData)
   (tail env D (NND_RegistryArgs.args v p m s r e t)))) := by
 apply NND_Entry1DecodeTransport.value base L D env v p m s r e t (unkey D.registry)
 intro entry
 exact NND_Entry1PdaValue.value base D env v p m s r e t entry

#print axioms value
end NND_Entry1DecodedValue
end

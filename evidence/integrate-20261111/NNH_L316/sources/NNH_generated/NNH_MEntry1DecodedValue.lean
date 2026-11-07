import NNH_MEntry1DecodeTransport
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry1DecodedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

def tail (env : RSL.Env) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (entry : RSL.EntryV1) : Except RSL.ProgramError Unit :=
 ebind (option (env.pda [RSL.SEED_ENTRY,a.master_account.key.bytes,RSL.PROFILE_BINDING.bytes,RSL.RELEASE_BINDING.bytes,[entry.bump]] D.registry) .invalidAccountData) fun expected =>
  eseq (echeck (decide (a.entry_account.key ≠ expected)) .invalidAccountData)
   (eseq (echeck (RSL.TX2_234.entryV1Bad a entry) .invalidAccountData) (.ok ()))

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id) (NNH_MEntry1Decode.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) e t) =
 ok (ebind (account e).bytes (fun b =>
  ebind (option ((NNH_MRegistryLibrary.install L).decodeEntryV1 b) .invalidAccountData)
   (tail env D (NNH_MRegistryArgs.args v p m s r e t)))) := by
 apply NNH_MEntry1DecodeTransport.value base L D env v p m s r e t (unkey D.registry)
 intro entry
 exact NNH_MEntry1PdaValue.value base D env v p m s r e t entry

#print axioms value
end NNH_MEntry1DecodedValue
end

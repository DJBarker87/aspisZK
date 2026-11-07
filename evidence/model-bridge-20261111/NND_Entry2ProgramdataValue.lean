import NND_Entry2ProgramdataSource
set_option autoImplicit false
noncomputable section
namespace NND_Entry2ProgramdataValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

def tail (env : RSL.Env) (a : RSL.TX2_234.Args) (entry : RSL.EntryV2) : Except RSL.ProgramError Unit :=
 ebind (option (env.pda [a.verifier_program.bytes,[entry.programdata_bump]] RSL.LOADER_ID) .invalidAccountData) fun vpd =>
  eseq (echeck (RSL.TX2_234.entryV2Bad a entry vpd) .invalidAccountData) (.ok ())

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) :
 outer (reply id) (NND_Entry2Programdata.run (NND_RegistryOps.install base D env) v m.key (unkey RSL.LOADER_ID) t (unkey RSL.LOADER_ID) entry) =
 ok (tail env (NND_RegistryArgs.args v p m s r e t) (entryV2 entry)) := by
 rw [NND_Entry2ProgramdataSource.source]
 have h := NND_PdaTransport.value env (NND_PdaSeeds.programdata v entry.programdata_bump) (unkey RSL.LOADER_ID)
  (NND_RegistryEntry2Check.check (NND_RegistryOps.install base D env) v m.key t (unkey RSL.LOADER_ID) entry) id
  (fun vpd => eseq (echeck (RSL.TX2_234.entryV2Bad (NND_RegistryArgs.args v p m s r e t) (entryV2 entry) vpd) .invalidAccountData) (.ok ()))
  (fun vpd => NND_Entry2ValueRSL.value base D env v p m s r e t entry vpd)
 rw [NND_PdaSeeds.programdata_bytes,key_forth] at h
 exact h

#print axioms value
end NND_Entry2ProgramdataValue
end

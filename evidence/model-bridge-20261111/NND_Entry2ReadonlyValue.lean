import NND_Entry2Readonly
import NND_Entry2DecodedValue
set_option autoImplicit false
noncomputable section
namespace NND_Entry2ReadonlyValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id) (NND_Entry2Readonly.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID)) =
 ok (eseq (RSL.readonlyAccount (account e) D.registry)
  (ebind (account e).data (fun b =>
   ebind (option ((NND_RegistryLibrary.install L).decodeEntryV2 b) .invalidAccountData)
    (NND_Entry2DecodedValue.tail env D (NND_RegistryArgs.args v p m s r e t))))) := by
 unfold NND_Entry2Readonly.run
 rw [NND_RegistryStd.readonly]
 have hr : RSL.readonlyAccount (account e) D.registry =
  if !decide (e.owner = unkey D.registry) || e.is_signer || e.is_writable || e.executable
  then .error .invalidAccountData else .ok () := by
  have hk : decide (key e.owner ≠ D.registry) = !decide (e.owner = unkey D.registry) := by
   calc
    _ = decide (key e.owner ≠ key (unkey D.registry)) := by rw [key_forth]
    _ = _ := (NND_CompareTransport.key_ne _ _).symm
  change (if decide (key e.owner ≠ D.registry) || e.is_signer || e.is_writable || e.executable then _ else _) = _
  rw [hk]
 rw [hr]
 cases h : (!decide (e.owner = unkey D.registry) || e.is_signer || e.is_writable || e.executable)
 · simp only [h,if_false,Bool.false_eq_true,bind_tc_ok]
   exact NND_Entry2DecodedValue.value base L D env v p m s r e t
 · rfl

#print axioms value
end NND_Entry2ReadonlyValue
end

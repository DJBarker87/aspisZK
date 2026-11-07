import NNH_MEntry1Readonly
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry1ReadonlyValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id) (NNH_MEntry1Readonly.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) e t) =
 ok (eseq (RSL.readonlyAccount (account e) D.registry)
  (ebind (account e).bytes (fun b =>
   ebind (option ((NNH_MRegistryLibrary.install L).decodeEntryV1 b) .invalidAccountData)
    (NNH_MEntry1DecodedValue.tail env D (NNH_MRegistryArgs.args v p m s r e t))))) := by
 unfold NNH_MEntry1Readonly.run
 rw [NNH_MRegistryStd.readonly]
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
   exact NNH_MEntry1DecodedValue.value base L D env v p m s r e t
 · rfl

#print axioms value
end NNH_MEntry1ReadonlyValue
end

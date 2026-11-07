import NND_RegistryV1Full
import NND_RegistryV2Full
import NND_ReadonlyPredicate
set_option autoImplicit false
noncomputable section
namespace NND_RegistryRouteValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env) : Except RSL.ProgramError Unit :=
 eseq (RSL.readonlyAccount a.registry_account D.registry)
 (if a.master.verifier_policy.flags &&& RSL.POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0
  then NND_RegistryEval.immutableValue (NND_RegistryLibrary.install L) D a env
  else NND_RegistryEval.v1Value (NND_RegistryLibrary.install L) D a env)

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id) (NND_RegistryFactor.tail (NND_RegistryOps.install base D env) v p m s r e t (unkey D.registry)) =
 ok (tail L D (NND_RegistryArgs.args v p m s r e t) env) := by
 rw [NND_RegistryBranches.source]
 unfold NND_RegistryBranches.route
 simp only [NND_RegistryScalarOps.from_bytes,bind_tc_ok]
 rw [NND_RegistryStd.readonly]
 have hr := NND_ReadonlyPredicate.value r (unkey D.registry)
 rw [key_forth] at hr
 unfold tail
 change _ = ok (eseq (RSL.readonlyAccount (account r) D.registry) _)
 rw [hr]
 cases hb : (!decide (r.owner = unkey D.registry) || r.is_signer || r.is_writable || r.executable)
 · simp only [hb,Bool.false_eq_true,if_false,bind_tc_ok,NND_RegistryScalarOps.deployment_flag,lift]
   have hf : (s.verifier_policy.flags &&& 2#u8 != 0#u8) =
    ((NND_RegistryArgs.args v p m s r e t).master.verifier_policy.flags &&& RSL.POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0) := by
    rw [NND_EntryRecordGuards.byte_bne]
    rfl
   rw [hf]
   split
   · exact NND_RegistryV2Full.value base L D env v p m s r e t
   · exact NND_RegistryV1Full.value base L D env v p m s r e t
 · rfl

#print axioms value
end NND_RegistryRouteValue
end

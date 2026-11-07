import NNH_MRegistryV1Full
import NNH_MRegistryV2Full
import NNH_MReadonlyPredicate
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryRouteValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env) : Except RSL.ProgramError Unit :=
 eseq (RSL.readonlyAccount a.registry_account D.registry)
 (if a.master.verifier_policy.flags &&& RSL.POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0
  then NNH_RegistryEval.immutableValue (NNH_MRegistryLibrary.install L) D a env
  else NNH_RegistryEval.v1Value (NNH_MRegistryLibrary.install L) D a env)

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id) (NND_RegistryFactor.tail (NNH_MRegistryOps.install base D env) v p m s r e t (unkey D.registry)) =
 ok (tail L D (NNH_MRegistryArgs.args v p m s r e t) env) := by
 rw [NND_RegistryBranches.source]
 unfold NND_RegistryBranches.route
 simp only [NNH_MRegistryScalarOps.from_bytes,bind_tc_ok]
 rw [NNH_MRegistryStd.readonly]
 have hr := NNH_MReadonlyPredicate.value r (unkey D.registry)
 rw [key_forth] at hr
 unfold tail
 change _ = ok (eseq (RSL.readonlyAccount (account r) D.registry) _)
 rw [hr]
 cases hb : (!decide (r.owner = unkey D.registry) || r.is_signer || r.is_writable || r.executable)
 · simp only [hb,Bool.false_eq_true,if_false,bind_tc_ok,NNH_MRegistryScalarOps.deployment_flag,lift]
   have hf : (s.verifier_policy.flags &&& 2#u8 != 0#u8) =
    ((NNH_MRegistryArgs.args v p m s r e t).master.verifier_policy.flags &&& RSL.POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0) := by
    rw [NNH_MEntryRecordGuards.byte_bne]
    rfl
   rw [hf]
   split
   · exact NNH_MRegistryV2Full.value base L D env v p m s r e t
   · exact NNH_MRegistryV1Full.value base L D env v p m s r e t
 · rfl

#print axioms value
end NNH_MRegistryRouteValue
end

import NMX_R3_RegistryPrefix0
import NMX_R3_RegistryPrefix1
import NMX_R3_RegistryPolicy
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryTop
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script000 (NMX_R3_RegistryOps.install base D env) v p m s reg ent t)) =
 RSL.TX2_234.Ref LIBB_PoolLib.library D (NMX_R3_RegistryArgs.args v p m s reg ent t) := by
 rw [NMX_R3_RegistryPrefix0.source,NMX_R3_RegistryArgs.policy_bad D v p m s reg ent t]
 have hp := NMX_R3_RegistryPolicy.fold base D env s.verifier_policy
  (NMX_R3_RegistryScriptParts.script001 (NMX_R3_RegistryOps.install base D env) v m s reg ent t (unkey D.registry))
  (NMX_R3_RegistryPrefix1.reference D (NMX_R3_RegistryArgs.args v p m s reg ent t))
  (NMX_R3_RegistryPrefix1.fold base D env v p m s reg ent t)
 unfold RSL.TX2_234.Ref
 cases bad : RSL.TX2_234.policyBad D (NMX_R3_RegistryArgs.args v p m s reg ent t) <;>
 simp only [bad,Bool.false_eq_true,↓reduceIte,RSL.RS.check,RSL.RS.seq,RSL.RS.bind_pure,
  RSL.RS.bind_throw,NMX_R3_RegistryEffectLaws.map_pure,reply]
 <;> first | exact hp | rfl
#print axioms fold
end NMX_R3_RegistryTop
end

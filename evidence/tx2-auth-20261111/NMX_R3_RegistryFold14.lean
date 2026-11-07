import NMX_R3_RegistryGuard14
import NMX_R3_RegistryFold15
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryFold14
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws

def tail (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (r : RSL.RegistryV1)
 (expected : RSL.B32) : RSL.RS Unit :=
 RSL.RS.seq (RSL.RS.check (decide (a.registry_account.key ≠ expected)) .invalidAccountData)
 (RSL.RS.seq (RSL.RS.check (RSL.TX2_234.registryV1Bad a r) .invalidAccountData)
 (RSL.RS.seq (RSL.RS.ofExcept (RSL.readonlyAccount a.entry_account D.registry))
  (NMX_R3_RegistryFold15.tail D a)))

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (r : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) (expected : solana_pubkey.Pubkey) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script014 (NMX_R3_RegistryOps.install base D env)
   v s reg ent t m.key (unkey D.registry) r expected)) =
 tail D (NMX_R3_RegistryArgs.args v p m s reg ent t) (registryV1 r) (key expected) := by
 rw [NMX_R3_RegistryGuard14.source,NND_CompareTransport.key_ne,
  NMX_R3_RegistryRecordGuards.registry1 v p m s reg ent t]
 have hn := NMX_R3_RegistryReadonly.fold base D env ent (unkey D.registry)
  (NMX_R3_RegistryScriptParts.script015 (NMX_R3_RegistryOps.install base D env) v ent t m.key (unkey D.registry))
  (NMX_R3_RegistryFold15.tail D (NMX_R3_RegistryArgs.args v p m s reg ent t))
  (NMX_R3_RegistryFold15.fold base D env v p m s reg ent t)
 rw [key_forth] at hn
 unfold tail
 rw [show (NMX_R3_RegistryArgs.args v p m s reg ent t).registry_account.key = key reg.key from rfl]
 cases hk : decide (key reg.key ≠ key expected) <;>
 cases hb : RSL.TX2_234.registryV1Bad (NMX_R3_RegistryArgs.args v p m s reg ent t) (registryV1 r) <;>
 simp only [hk,hb,Bool.false_or,Bool.true_or,Bool.false_eq_true,↓reduceIte,
  map_pure,reply,RSL.RS.check,RSL.RS.seq,RSL.RS.bind_pure,RSL.RS.bind_throw]
 <;> first | exact hn | rfl
#print axioms fold
end NMX_R3_RegistryFold14
end

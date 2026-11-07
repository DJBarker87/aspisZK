import NMX_R3_RegistryGuard6
import NMX_R3_RegistryFold7
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryFold6
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws

def tail (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (r : RSL.RegistryV2) (rpd : RSL.B32) : RSL.RS Unit :=
 RSL.RS.seq (RSL.RS.check (RSL.TX2_234.registryV2Bad D a r rpd) .invalidAccountData)
 (RSL.RS.seq (RSL.RS.ofExcept (RSL.readonlyAccount a.entry_account D.registry))
  (NMX_R3_RegistryFold7.tail D a))

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (r : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (rpd : solana_pubkey.Pubkey) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script006 (NMX_R3_RegistryOps.install base D env)
   v s ent t (unkey RSL.LOADER_ID) m.key (unkey D.registry) r rpd)) =
 tail D (NMX_R3_RegistryArgs.args v p m s reg ent t) (registryV2 r) (key rpd) := by
 rw [NMX_R3_RegistryGuard6.source,NMX_R3_RegistryRecordGuards.registry2 D v p m s reg ent t]
 have hn := NMX_R3_RegistryReadonly.fold base D env ent (unkey D.registry)
  (NMX_R3_RegistryScriptParts.script007 (NMX_R3_RegistryOps.install base D env)
   v ent t (unkey RSL.LOADER_ID) (unkey RSL.LOADER_ID) m.key (unkey D.registry))
  (NMX_R3_RegistryFold7.tail D (NMX_R3_RegistryArgs.args v p m s reg ent t))
  (NMX_R3_RegistryFold7.fold base D env v p m s reg ent t)
 rw [key_forth] at hn
 unfold tail
 cases hb : RSL.TX2_234.registryV2Bad D (NMX_R3_RegistryArgs.args v p m s reg ent t) (registryV2 r) (key rpd) <;>
 simp only [hb,Bool.false_eq_true,↓reduceIte,NMX_R3_RegistryEffectLaws.map_pure,reply,
  RSL.RS.check,RSL.RS.seq,RSL.RS.bind_pure,RSL.RS.bind_throw]
 <;> first | exact hn | rfl
#print axioms fold
end NMX_R3_RegistryFold6
end

import NMX_R3_RegistryPda005
import NMX_R3_RegistryFold6
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryFold5
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws

def tail (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (e : RSL.RegistryV2) (expected : RSL.B32) : RSL.RS Unit :=
 RSL.RS.seq (RSL.RS.check (decide (a.registry_account.key ≠ expected)) .invalidAccountData)
  (RSL.RS.bind (RSL.pdaOrErr [D.registry.bytes,[e.programdata_bump]] RSL.LOADER_ID)
   (NMX_R3_RegistryFold6.tail D a e))

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (e : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (expected : solana_pubkey.Pubkey) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script005 (NMX_R3_RegistryOps.install base D env)
   v s reg ent t (unkey RSL.LOADER_ID) m.key (unkey D.registry) e expected)) =
 tail D (NMX_R3_RegistryArgs.args v p m s reg ent t) (registryV2 e) (key expected) := by
 rw [NMX_R3_RegistryPda005.source,NND_CompareTransport.key_ne]
 have hp := NMX_R3_RegistryPdaLaw.fold (NMX_R3_PdaSeeds.programdata (unkey D.registry) e.programdata_bump)
  (unkey RSL.LOADER_ID) _
  (NMX_R3_RegistryFold6.tail D (NMX_R3_RegistryArgs.args v p m s reg ent t) (registryV2 e))
  (fun vpd => NMX_R3_RegistryFold6.fold base D env v p m s reg ent t e vpd)
 simp only [NMX_R3_PdaSeeds.programdata_bytes,key_forth] at hp
 unfold tail
 rw [show (NMX_R3_RegistryArgs.args v p m s reg ent t).registry_account.key = key reg.key from rfl]
 cases hk : decide (key reg.key ≠ key expected) <;>
 simp only [hk,Bool.false_eq_true,↓reduceIte,NMX_R3_RegistryEffectLaws.map_pure,reply,
  RSL.RS.check,RSL.RS.seq,RSL.RS.bind_pure,RSL.RS.bind_throw]
 <;> first | exact hp | rfl
#print axioms fold
end NMX_R3_RegistryFold5
end

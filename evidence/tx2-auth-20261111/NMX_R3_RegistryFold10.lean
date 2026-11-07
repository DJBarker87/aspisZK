import NMX_R3_RegistryPda010
import NMX_R3_RegistryLeaf2Canonical
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryFold10
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws

def tail (a : RSL.TX2_234.Args) (e : RSL.EntryV2) (expected : RSL.B32) : RSL.RS Unit :=
 RSL.RS.seq (RSL.RS.check (decide (a.entry_account.key ≠ expected)) .invalidAccountData)
  (RSL.RS.bind (RSL.pdaOrErr [a.verifier_program.bytes,[e.programdata_bump]] RSL.LOADER_ID)
   (NMX_R3_RegistryLeaf2Canonical.tail a e))

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (e : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (expected : solana_pubkey.Pubkey) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script010 (NMX_R3_RegistryOps.install base D env)
   v ent t (unkey RSL.LOADER_ID) (unkey RSL.LOADER_ID) m.key e expected)) =
 tail (NMX_R3_RegistryArgs.args v p m s reg ent t) (entryV2 e) (key expected) := by
 rw [NMX_R3_RegistryPda010.source,NND_CompareTransport.key_ne]
 have hp := NMX_R3_RegistryPdaLaw.fold (NMX_R3_PdaSeeds.programdata v e.programdata_bump)
  (unkey RSL.LOADER_ID) _
  (NMX_R3_RegistryLeaf2Canonical.tail (NMX_R3_RegistryArgs.args v p m s reg ent t) (entryV2 e))
  (fun vpd => NMX_R3_RegistryLeaf2Canonical.fold base D env v p m s reg ent t e vpd)
 rw [NMX_R3_PdaSeeds.programdata_bytes,key_forth] at hp
 unfold tail
 rw [show (NMX_R3_RegistryArgs.args v p m s reg ent t).entry_account.key = key ent.key from rfl]
 cases hk : decide (key ent.key ≠ key expected) <;>
 simp only [hk,Bool.false_eq_true,↓reduceIte,NMX_R3_RegistryEffectLaws.map_pure,reply,
  RSL.RS.check,RSL.RS.seq,RSL.RS.bind_pure,RSL.RS.bind_throw]
 <;> first | exact hp | rfl
#print axioms fold
end NMX_R3_RegistryFold10
end

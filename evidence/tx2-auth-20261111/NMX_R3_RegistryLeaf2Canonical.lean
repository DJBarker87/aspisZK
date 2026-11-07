import NMX_R3_RegistryPureLeaf2
import NMX_R3_RegistryEntry2Value
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryLeaf2Canonical
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier
open NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws

def tail (a : RSL.TX2_234.Args) (e : RSL.EntryV2) (vpd : RSL.B32) : RSL.RS Unit :=
 RSL.RS.seq (RSL.RS.check (RSL.TX2_234.entryV2Bad a e vpd) .invalidAccountData) (RSL.RS.pure ())

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (e : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2)
 (vpd : solana_pubkey.Pubkey) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script011 (NMX_R3_RegistryOps.install base D env)
   v t (unkey RSL.LOADER_ID) m.key e vpd)) =
 tail (NMX_R3_RegistryArgs.args v p m s reg ent t) (entryV2 e) (key vpd) := by
 rw [NMX_R3_RegistryPureLeaf2.step011]
 change RSL.Spec.map (reply id) (scalarSpec
  (NMX_R3_RegistryEntry2Check.check (NMX_R3_RegistryOps.install base D env)
   v m.key t (unkey RSL.LOADER_ID) e vpd)) = _
 rw [NMX_R3_RegistryEntry2Value.value,NMX_R3_EntryV2Guard.value v p m s reg ent t]
 unfold tail
 cases hb : RSL.TX2_234.entryV2Bad (NMX_R3_RegistryArgs.args v p m s reg ent t) (entryV2 e) (key vpd) <;>
 simp only [hb,Bool.false_eq_true,↓reduceIte,scalarSpec,map_pure,reply,
  RSL.RS.check,RSL.RS.seq,RSL.RS.bind_pure,RSL.RS.bind_throw]
 <;> rfl
#print axioms fold
end NMX_R3_RegistryLeaf2Canonical
end

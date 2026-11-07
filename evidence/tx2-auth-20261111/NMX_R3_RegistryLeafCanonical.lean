import NMX_R3_RegistryPureLeaves
import NMX_R3_RegistryEntry1Value
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryLeafCanonical
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier
open NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws

def entry1 (a : RSL.TX2_234.Args) (e : RSL.EntryV1) (expected : RSL.B32) : RSL.RS Unit :=
 RSL.RS.seq (RSL.RS.check (decide (a.entry_account.key ≠ expected)) .invalidAccountData)
  (RSL.RS.seq (RSL.RS.check (RSL.TX2_234.entryV1Bad a e) .invalidAccountData) (RSL.RS.pure ()))

theorem leaf1 (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (e : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1)
 (expected : solana_pubkey.Pubkey) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script018 (NMX_R3_RegistryOps.install base D env)
   v ent t m.key e expected)) =
 entry1 (NMX_R3_RegistryArgs.args v p m s reg ent t) (entryV1 e) (key expected) := by
 rw [NMX_R3_RegistryPureLeaves.step018]
 change RSL.Spec.map (reply id) (scalarSpec
  (NMX_R3_RegistryEntry1Check.check (NMX_R3_RegistryOps.install base D env)
   v m.key ent t e expected)) = _
 rw [NMX_R3_RegistryEntry1Value.value,NND_CompareTransport.key_ne,
  NMX_R3_EntryRecordGuards.entry1 v p m s reg ent t]
 unfold entry1
 rw [show (NMX_R3_RegistryArgs.args v p m s reg ent t).entry_account.key = key ent.key from rfl]
 cases hk : decide (key ent.key ≠ key expected) <;>
 cases hb : RSL.TX2_234.entryV1Bad (NMX_R3_RegistryArgs.args v p m s reg ent t) (entryV1 e) <;>
 simp only [hk,hb,Bool.false_or,Bool.true_or,Bool.false_eq_true,↓reduceIte,
  scalarSpec,map_pure,reply,RSL.RS.check,RSL.RS.seq,RSL.RS.bind_pure,RSL.RS.bind_throw]
 <;> rfl
#print axioms leaf1
end NMX_R3_RegistryLeafCanonical
end

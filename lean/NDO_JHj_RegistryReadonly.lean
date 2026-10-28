import NDO_JHj_KeyComparison
import NDO_JHg_AuditWorld
import NDO_JHb_Owners
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_RegistryReadonly
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
attribute [local irreducible] JHg_World.e2

theorem shared (base : Ops) (key : solana_pubkey.Pubkey) :
    core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (JHd_ReferenceSlots.install base)) key key=ok false :=
  JHj_KeyComparison.different base key
#print axioms shared

theorem registry (base : Ops) : r1_pool_adapter.owned.require_readonly_account
    (JHd_ReferenceSlots.install base) (JHg_World.e2.snapshot 4 128 256) JHb_Programs.registry=ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.require_readonly_account r1_pool_adapter.owned.OwnedAccount.impl.owner
  rw [JHg_AuditWorld.owner,JHb_Owners.registry,bind_tc_ok]
  unfold r1_pool_adapter.readonly_meta_ok
  rw [shared,bind_tc_ok]
  simp only [JHg_AuditWorld.signer,JHg_AuditWorld.writable,JHg_AuditWorld.executable]
  rfl
#print axioms registry

theorem entry (base : Ops) : r1_pool_adapter.owned.require_readonly_account
    (JHd_ReferenceSlots.install base) (JHg_World.e2.snapshot 5 192 320) JHb_Programs.registry=ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.require_readonly_account r1_pool_adapter.owned.OwnedAccount.impl.owner
  rw [JHg_AuditWorld.owner,JHb_Owners.entry,bind_tc_ok]
  unfold r1_pool_adapter.readonly_meta_ok
  rw [shared,bind_tc_ok]
  simp only [JHg_AuditWorld.signer,JHg_AuditWorld.writable,JHg_AuditWorld.executable]
  rfl
#print axioms entry
end AspisR1.JHj_RegistryReadonly
end

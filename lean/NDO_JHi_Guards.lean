import NDO_JHg_AuditWorld
import NDO_JHd_NativeGuards
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_Guards
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers
open _root_.AdapterRw
attribute [local irreducible] JHg_World.e2 JHb_World.e2

theorem proof : r1_pool_adapter.owned.require_readonly_buffer
    (JHg_World.e2.snapshot 0 58295 58295)=ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.require_readonly_buffer
  simp only [JHg_AuditWorld.signer,JHg_AuditWorld.writable,JHg_AuditWorld.executable]
  rfl
#print axioms proof

theorem readonly (base : Ops) (a x y : Nat)
    (owner : (JHg_World.e2.snapshot a x y).owner=JHb_Programs.pool) :
    r1_pool_adapter.owned.require_readonly_account (JHd_KeyStd.install base)
      (JHg_World.e2.snapshot a x y) JHb_Programs.pool=ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.require_readonly_account r1_pool_adapter.owned.OwnedAccount.impl.owner
  rw [owner,bind_tc_ok]
  unfold r1_pool_adapter.readonly_meta_ok
  rw [JHd_NativeGuards.pool_compare,bind_tc_ok]
  simp only [JHg_AuditWorld.signer,JHg_AuditWorld.writable,JHg_AuditWorld.executable]
  rfl
#print axioms readonly

theorem master (base : Ops) : r1_pool_adapter.owned.require_readonly_account
    (JHd_KeyStd.install base) (JHg_World.e2.snapshot 1 384 384) JHb_Programs.pool=ok (.Ok ()) :=
  readonly base 1 384 384 ((JHg_AuditWorld.owner _ _ _).trans JHb_Owners.master)
#print axioms master

theorem forest (base : Ops) : r1_pool_adapter.owned.require_readonly_account
    (JHd_KeyStd.install base) (JHg_World.e2.snapshot 2 192 192) JHb_Programs.pool=ok (.Ok ()) :=
  readonly base 2 192 192 ((JHg_AuditWorld.owner _ _ _).trans JHb_Owners.forest)
#print axioms forest

theorem lane (base : Ops) : r1_pool_adapter.owned.require_readonly_account
    (JHd_KeyStd.install base) (JHg_World.e2.snapshot 3 768 768) JHb_Programs.pool=ok (.Ok ()) :=
  readonly base 3 768 768 ((JHg_AuditWorld.owner _ _ _).trans JHb_Owners.lane)
#print axioms lane
end AspisR1.JHi_Guards
end

import NDO_JHb_Owners
import JHb_GuardStd
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_Guards
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers JHb_World
attribute [local irreducible] e1 e2

theorem proof : AdapterRw.r1_pool_adapter.owned.require_readonly_buffer (e2.snapshot 0 58295 58295)=ok (.Ok ()) := by
  unfold AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
  unfold e2
  change AdapterRw.r1_pool_adapter.readonly_buffer_meta_ok false false false=ok (.Ok ())
  rfl
#print axioms proof

theorem master (base : AdapterRw.Ops) : AdapterRw.r1_pool_adapter.owned.require_readonly_account
    (Hist_Authority.install base) (e2.snapshot 1 384 384) JHb_Programs.pool=ok (.Ok ()) := by
  rw [← JHb_Owners.master]
  apply JHb_GuardStd.readonly <;> unfold e2 <;> rfl
#print axioms master

theorem forest (base : AdapterRw.Ops) : AdapterRw.r1_pool_adapter.owned.require_readonly_account
    (Hist_Authority.install base) (e2.snapshot 2 192 192) JHb_Programs.pool=ok (.Ok ()) := by
  rw [← JHb_Owners.forest]
  apply JHb_GuardStd.readonly <;> unfold e2 <;> rfl
#print axioms forest

theorem lane (base : AdapterRw.Ops) : AdapterRw.r1_pool_adapter.owned.require_readonly_account
    (Hist_Authority.install base) (e2.snapshot 3 768 768) JHb_Programs.pool=ok (.Ok ()) := by
  rw [← JHb_Owners.lane]
  apply JHb_GuardStd.readonly <;> unfold e2 <;> rfl
#print axioms lane
end AspisR1.JHb_Guards
end

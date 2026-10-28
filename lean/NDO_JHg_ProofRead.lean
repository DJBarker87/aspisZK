import NDO_JHg_AuditWorld
import JGx_EntryReads
import NDO_JHd_ReferenceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHg_ProofRead
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers JHg_World
attribute [local irreducible] e2 JHb_Header.account

theorem first (base : AdapterRw.Ops) : (JHd_ReferenceSlots.install base).op9 (e2.second secondSizes)=
    ok (some (e2.snapshot 0 58295 58295)) := rfl
#print axioms first

theorem data (ops : AdapterRw.Ops) : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
    (e2.snapshot 0 58295 58295)=ok (.Ok JHb_Header.account) := by
  have b := JHg_AuditWorld.proof
  have len : (e2.buffers (e2.handles 0).1).val.length=58295 := by
    rw [b]
    exact JHb_Header.length
  rw [JGx_EntryReads.data ops e2 0 58295 58295 (Or.inl len),b]
#print axioms data
end AspisR1.JHg_ProofRead
end

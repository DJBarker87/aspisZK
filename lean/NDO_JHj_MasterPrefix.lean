import NDO_JHj_MasterGuards
import NDO_JHj_MasterPda
import NDO_JHj_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_MasterPrefix
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_AccountValues.master JHj_Seeds.key JHj_Seeds.master

theorem source (base : Ops) (slot : U64) :
    JHd_Authentication.afterMaster (JHd_ReferenceSlots.install base)
      CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master=
    JHj_MasterPda.run (JHd_ReferenceSlots.install base)
      CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master
      JHj_Seeds.key JHj_Seeds.master := by
  unfold JHd_Authentication.afterMaster
  simp only [r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok]
  change (ok (e2.snapshot 1 384 384).key >>= _) = _
  rw [bind_tc_ok,JHj_MasterGuards.pool,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  rw [JHj_MasterGuards.mask,bind_tc_ok,JHj_MasterGuards.mask_matches]
  simp only [Bool.false_eq_true,if_false]
  unfold JHj_MasterPda.run JHj_Seeds.master JHj_Seeds.key
  simp only [JHd_ReferenceSlots.install,JHd_KeyStd.install,JGx_MagicStd.install,
    JHd_ReferenceSlots.leaves,lift,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JHj_MasterPrefix
end

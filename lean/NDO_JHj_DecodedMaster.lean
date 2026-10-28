import NDO_JHi_AuthenticationPrefix
import NDO_JHj_MasterPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_DecodedMaster
open Aeneas Aeneas.Std Result S2W_D189Wrappers
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_DataMaster.value

theorem source (base : Ops) (slot : U64)
    (decoded : (JHd_ReferenceSlots.install base).op48 JHg_DataMaster.value=ok (.Ok JHg_AccountValues.master)) :
    r1_pool_adapter.owned.authenticate_asq8_accounts (JHd_ReferenceSlots.install base)
      CPH_Program.verifier (e2.second secondSizes) JHb_Programs.pool 3#u8 slot=
    JHj_MasterPda.run (JHd_ReferenceSlots.install base)
      CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master
      JHj_Seeds.key JHj_Seeds.master := by
  have hp := JHi_AuthenticationPrefix.source (JHd_ReferenceSlots.leaves base) 3#u8 slot
  change r1_pool_adapter.owned.authenticate_asq8_accounts (JHd_ReferenceSlots.install base)
    CPH_Program.verifier (e2.second secondSizes) JHb_Programs.pool 3#u8 slot = _ at hp
  rw [hp]
  unfold JHi_Authentication.afterRead
  change (JHd_KeyStd.install (JHd_ReferenceSlots.leaves base)).op48 JHg_DataMaster.value=
    ok (.Ok JHg_AccountValues.master) at decoded
  rw [decoded,bind_tc_ok]
  exact JHj_MasterPrefix.source base slot
#print axioms source
end AspisR1.JHj_DecodedMaster
end

import NDO_JHj_EntryChecks
import NDO_JHj_EntryFields
import NDO_JHd_ReferenceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_EntryChecks
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
attribute [local irreducible] JHg_World.e2 JHj_Seeds.key JHj_RegistryValue.loader
  JHj_RegistryValue.verifierProgramdata

theorem source (base : Ops) (slot : U64)
    (active : (JHd_ReferenceSlots.install base).op29 JHj_RegistryValue.entry slot=ok true) :
    JHj_EntryChecks.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool
      (JHg_World.e2.snapshot 1 384 384) JHg_AccountValues.master
      (JHg_World.e2.snapshot 4 128 256) (JHg_World.e2.snapshot 5 192 320) slot
      JHb_Programs.registry JHj_RegistryValue.loader JHj_Seeds.key JHj_RegistryValue.loader
      JHj_RegistryValue.entry JHj_RegistryValue.verifierProgramdata=ok (.Ok ()) := by
  unfold JHj_EntryChecks.run
  change (ok JHj_Seeds.key >>= _) = _
  rw [bind_tc_ok,JHj_EntryFields.pool,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  rw [JHj_EntryFields.policy_binding,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  change (ok CPH_Program.verifier >>= _) = _
  rw [bind_tc_ok,JHj_EntryFields.verifier_program,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  rw [JHj_EntryFields.profile_binding,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  rw [JHj_EntryFields.release_binding,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  change (ok 1#u8 >>= _) = _
  rw [bind_tc_ok]
  change (if (1#u8 != 1#u8) then _ else _)=_
  simp only [show (1#u8 != 1#u8)=false from Eq.refl _,Bool.false_eq_true,ite_false]
  rw [JHj_EntryFields.loader_program,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  change (ok JHj_RegistryValue.verifierProgramdata >>= _) = _
  rw [bind_tc_ok,JHj_EntryFields.programdata_address,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  rw [JHj_EntryFields.expected_upgrade_authority,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  rw [active,bind_tc_ok]
  exact Eq.refl _
#print axioms source
end AspisR1.JHv_EntryChecks
end

import NDO_JHj_RegistryPolicy
import NDO_JHj_RegistryGuards
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_RegistryPrefix
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_AccountValues.master

theorem source (base : Ops) (slot : U64) :
    r1_pool_adapter.owned.authenticate_invariant_release_registry (JHd_ReferenceSlots.install base)
      CPH_Program.verifier JHb_Programs.pool (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot=
    JHj_RegistryPolicy.run (JHd_ReferenceSlots.install base)
      CPH_Program.verifier JHb_Programs.pool (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot JHb_Programs.registry := by
  unfold r1_pool_adapter.owned.authenticate_invariant_release_registry
  change (ok JHb_Programs.pool >>= _) = _
  rw [bind_tc_ok]
  change (ok JHb_Programs.pool >>= _) = _
  rw [bind_tc_ok,JHj_RegistryGuards.pool,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  change (ok 1#u8 >>= _) = _
  rw [bind_tc_ok]
  rw [JHj_RegistryGuards.registry_flag]
  simp only [lift,bind_tc_ok]
  simp only [show (3#u8 &&& 1#u8 =0#u8) ↔ False from by decide,if_false]
  change (ok JHb_Programs.registry >>= _) = _
  rw [bind_tc_ok,JHj_RegistryGuards.program,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  rw [JHj_RegistryGuards.authority,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  rw [JHj_RegistryGuards.policy,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  rfl
#print axioms source
end AspisR1.JHj_RegistryPrefix
end

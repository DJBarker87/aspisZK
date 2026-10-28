import NDO_JHj_RegistryPolicy
import NDO_JHj_RegistryRead
import NDO_JHj_RegistryReadonly
import NDO_JHj_RegistryValue
import NDO_JHj_RegistryGuards
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_RegistryPolicyStep
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_AccountValues.master

theorem source (base : Ops) (slot : U64)
    (validated : (JHd_ReferenceSlots.install base).op15 JHg_AccountValues.master.verifier_policy=ok (.Ok ()))
    (loader : (JHd_ReferenceSlots.install base).op41=ok JHj_RegistryValue.loader) :
    JHj_RegistryPolicy.run (JHd_ReferenceSlots.install base)
      CPH_Program.verifier JHb_Programs.pool (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot JHb_Programs.registry=
    JHj_RegistryRead.run (JHd_ReferenceSlots.install base)
      CPH_Program.verifier JHb_Programs.pool (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot JHb_Programs.registry JHj_RegistryValue.loader := by
  unfold JHj_RegistryPolicy.run
  rw [validated,bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  change (ok JHb_Programs.registry >>= _) = _
  rw [bind_tc_ok,JHj_RegistryReadonly.registry,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  change (ok 2#u8 >>= _) = _
  rw [bind_tc_ok,JHj_RegistryGuards.deployment_flag]
  simp only [lift,bind_tc_ok]
  simp only [show (3#u8 &&& 2#u8 !=0#u8)=true from rfl,if_true]
  rw [loader,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JHj_RegistryPolicyStep
end

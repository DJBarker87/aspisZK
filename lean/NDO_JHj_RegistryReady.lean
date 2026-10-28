import NDO_JHj_RegistryPrefix
import NDO_JHj_RegistryPolicyStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_RegistryReady
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_AccountValues.master

/-- Complete corrected-world registry prefix through its real account read.
Only actual policy validation and loader ID remain in this prefix theorem. -/
theorem source (base : Ops) (slot : U64)
    (validated : (JHd_ReferenceSlots.install base).op15 JHg_AccountValues.master.verifier_policy=ok (.Ok ()))
    (loader : (JHd_ReferenceSlots.install base).op41=ok JHj_RegistryValue.loader) :
    r1_pool_adapter.owned.authenticate_invariant_release_registry (JHd_ReferenceSlots.install base)
      CPH_Program.verifier JHb_Programs.pool (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot=
    JHj_RegistryRead.run (JHd_ReferenceSlots.install base)
      CPH_Program.verifier JHb_Programs.pool (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot JHb_Programs.registry JHj_RegistryValue.loader := by
  rw [JHj_RegistryPrefix.source,JHj_RegistryPolicyStep.source base slot validated loader]
#print axioms source
end AspisR1.JHj_RegistryReady
end

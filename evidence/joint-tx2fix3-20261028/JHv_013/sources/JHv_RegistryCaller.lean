import JHv_RegistryDecoded
import JHj_RegistryReady
import JHj_RegistryReadStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_RegistryCaller
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2 JHj_Seeds.key JHj_RegistryValue.loader

theorem source (base : Ops) (slot : U64) (runtime : FixturePdaRuntime base)
    (validated : (JHd_ReferenceSlots.install base).op15 JHg_AccountValues.master.verifier_policy=ok (.Ok ()))
    (loader : (JHd_ReferenceSlots.install base).op41=ok JHj_RegistryValue.loader)
    (registry : (JHd_ReferenceSlots.install base).op33 JHb_DataRegistry.value=ok (.Ok JHj_RegistryValue.registry))
    (immutable : (JHd_ReferenceSlots.install base).op28 JHj_RegistryValue.registry=ok true)
    (unrevoked : (JHd_ReferenceSlots.install base).op27 JHj_RegistryValue.registry=ok false)
    (decoded : (JHd_ReferenceSlots.install base).op34 JHb_DataEntry.value=ok (.Ok JHj_RegistryValue.entry))
    (active : (JHd_ReferenceSlots.install base).op29 JHj_RegistryValue.entry slot=ok true) :
    r1_pool_adapter.owned.authenticate_invariant_release_registry (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool
      (JHg_World.e2.snapshot 1 384 384) JHg_AccountValues.master
      (JHg_World.e2.snapshot 4 128 256) (JHg_World.e2.snapshot 5 192 320) slot
      =ok (.Ok ()) := by
  rw [JHj_RegistryReady.source base slot validated loader,
    JHj_RegistryReadStep.source base slot registry]
  exact JHv_RegistryDecoded.source base slot runtime immutable unrevoked decoded active
#print axioms source
end AspisR1.JHv_RegistryCaller
end

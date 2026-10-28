import NDO_NCX_RegistryFixture
import NDO_NCX_EntryFixture
import NCX_Install
import NDO_JHj_RegistryValue
set_option autoImplicit false
namespace NCX_FixtureCarriers
open Aeneas Aeneas.Std Result AspisR1
attribute [local irreducible] JHb_DataRegistry.bytes JHb_DataEntry.bytes
theorem registry_pool : NCX_RegistryFields.pool=JHj_RegistryValue.registry.pool := by
  apply Subtype.ext
  exact JHg_AuditRegistry.pool.symm.trans JHg_BindingsRegistry.pool
#print axioms registry_pool
theorem registry_policy : NCX_RegistryFields.policy=JHj_RegistryValue.registry.policy_binding := by
  apply Subtype.ext
  exact JHg_AuditRegistry.policy.symm.trans JHg_BindingsRegistry.policy
#print axioms registry_policy
theorem registry_program : NCX_RegistryFields.program=JHj_RegistryValue.registry.registry_program := by
  apply Subtype.ext
  exact JHg_AuditRegistry.program.symm.trans JHg_BindingsRegistry.program
#print axioms registry_program
theorem registry_loader : NCX_RegistryFields.loader=JHj_RegistryValue.registry.loader_program := by
  apply Subtype.ext
  exact JHg_AuditRegistry.loader.symm
#print axioms registry_loader
theorem registry_programdata : NCX_RegistryFields.programdata=JHj_RegistryValue.registry.programdata_address := by
  apply Subtype.ext
  exact JHg_AuditRegistry.programdata.symm
#print axioms registry_programdata
theorem registry : NCX_Carrier.registry NCX_RegistryValue.value=JHj_RegistryValue.registry := by
  simp only [NCX_Carrier.registry,NCX_RegistryValue.value,
    registry_pool,registry_policy,registry_program,registry_loader,registry_programdata]
  rfl
#print axioms registry
theorem entry_pool : NCX_EntryFields.pool=JHj_RegistryValue.entry.pool := by
  apply Subtype.ext
  exact JHg_AuditEntry.pool.symm.trans JHg_BindingsRegistry.entry_pool
#print axioms entry_pool
theorem entry_verifier : NCX_EntryFields.verifier=JHj_RegistryValue.entry.verifier_program := by
  apply Subtype.ext
  exact JHg_AuditEntry.verifier.symm.trans JHg_BindingsRegistry.verifier
#print axioms entry_verifier
theorem entry_profile : NCX_EntryFields.profile=JHj_RegistryValue.entry.profile_binding := by
  apply Subtype.ext
  exact JHg_AuditEntry.profile.symm.trans JHg_BindingsRegistry.profile
#print axioms entry_profile
theorem entry_release : NCX_EntryFields.release=JHj_RegistryValue.entry.release_binding := by
  apply Subtype.ext
  exact JHg_AuditEntry.release.symm.trans JHg_BindingsRegistry.release
#print axioms entry_release
theorem entry_policy : NCX_EntryFields.policy=JHj_RegistryValue.entry.policy_binding := by
  apply Subtype.ext
  exact JHg_AuditEntry.policy.symm.trans JHg_BindingsRegistry.entry_policy
#print axioms entry_policy
theorem entry_loader : NCX_EntryFields.loader=JHj_RegistryValue.entry.loader_program := by
  apply Subtype.ext
  exact JHg_AuditRegistry.loader.symm
#print axioms entry_loader
theorem entry_programdata : NCX_EntryFields.programdata=JHj_RegistryValue.entry.programdata_address := by
  apply Subtype.ext
  exact JHg_AuditEntry.programdata.symm
#print axioms entry_programdata
theorem entry : NCX_Carrier.entry NCX_EntryValue.value=JHj_RegistryValue.entry := by
  simp only [NCX_Carrier.entry,NCX_EntryValue.value,
    entry_pool,entry_verifier,entry_profile,entry_release,entry_policy,entry_loader,entry_programdata]
  rfl
#print axioms entry
end NCX_FixtureCarriers

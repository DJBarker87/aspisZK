import NDO_JHj_RegistryValue
import NDO_JHj_RegistryGuards
set_option autoImplicit false
namespace AspisR1.JHj_RegistryFields
open Aeneas Aeneas.Std Result

theorem pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.registry.pool (JHj_Seeds.key)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms pool

theorem authority : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.registry.authority (JHg_AccountValues.master.verifier_policy.registry_authority)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms authority

theorem policy_binding : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.registry.policy_binding (JHg_AccountValues.master.verifier_policy.policy_binding)=ok false := by
  unfold JHj_RegistryValue.registry AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms policy_binding

theorem registry_program : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.registry.registry_program (JHb_Programs.registry)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms registry_program

theorem loader_program : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.registry.loader_program (JHj_RegistryValue.loader)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms loader_program

theorem programdata_address : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.registry.programdata_address (JHj_RegistryValue.registryProgramdata)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms programdata_address
end AspisR1.JHj_RegistryFields

import NDO_JHj_RegistryValue
import NDO_JHj_RegistryGuards
set_option autoImplicit false
namespace AspisR1.JHj_EntryFields
open Aeneas Aeneas.Std Result

theorem pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.entry.pool (JHj_Seeds.key)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms pool

theorem policy_binding : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.entry.policy_binding (AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms policy_binding

theorem verifier_program : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.entry.verifier_program (CPH_Program.verifier)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms verifier_program

theorem profile_binding : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.entry.profile_binding (AdapterRw.r1_pool_adapter.PROFILE_BINDING)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms profile_binding

theorem release_binding : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.entry.release_binding (AdapterRw.r1_pool_adapter.RELEASE_BINDING)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms release_binding

theorem loader_program : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.entry.loader_program (JHj_RegistryValue.loader)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms loader_program

theorem programdata_address : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.entry.programdata_address (JHj_RegistryValue.verifierProgramdata)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms programdata_address

theorem expected_upgrade_authority : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHj_RegistryValue.entry.expected_upgrade_authority (Array.repeat 32#usize 0#u8)=ok false := by
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms expected_upgrade_authority
end AspisR1.JHj_EntryFields

import NDO_JHj_MasterGuards
set_option autoImplicit false
namespace AspisR1.JHj_RegistryGuards
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHb_Programs.pool JHb_Programs.pool=ok false :=
  S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms pool

theorem program : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHg_AccountValues.master.verifier_policy.registry_program JHb_Programs.registry=ok false :=
  S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms program

theorem authority : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHg_AccountValues.master.verifier_policy.registry_authority (Array.repeat 32#usize 0#u8)=ok false :=
  S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms authority

theorem policy : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHg_AccountValues.master.verifier_policy.policy_binding r1_pool_adapter.AUDIT_POLICY_BINDING=ok false := by
  have eq : JHg_AccountValues.master.verifier_policy.policy_binding=r1_pool_adapter.AUDIT_POLICY_BINDING := by
    unfold r1_pool_adapter.AUDIT_POLICY_BINDING
    rfl
  rw [eq]
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms policy

theorem registry_flag : JHg_AccountValues.master.verifier_policy.flags &&& 1#u8=3#u8 &&& 1#u8 := rfl
#print axioms registry_flag

theorem deployment_flag : JHg_AccountValues.master.verifier_policy.flags &&& 2#u8=3#u8 &&& 2#u8 := rfl
#print axioms deployment_flag
end AspisR1.JHj_RegistryGuards

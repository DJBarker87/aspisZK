import LPi_TowerValues
set_option autoImplicit false
namespace AspisR1.LPi_MixedValues
open Aeneas Aeneas.Std Result LPi_FieldValues

theorem cm_m31 (x : NC) (s : U32) : ∃ z,
    FIo_Native.aspis_core.field.CM31.mul_m31 x s = ok z ∧ canonC z ∧
      cw z = ((x.a.val*s.val)%2147483647,(x.b.val*s.val)%2147483647) := by
  obtain ⟨a,ha,va,ca⟩ := LPf_BaseMultiply.source x.a s
  obtain ⟨b,hb,vb,cb⟩ := LPf_BaseMultiply.source x.b s
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.mul_m31,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

theorem qm_m31 (x : NQ) (s : U32) : ∃ z,
    FIo_Native.aspis_core.field.QM31.mul_m31 x s = ok z ∧ canonQ z ∧
      qw z = (((x.c0.a.val*s.val)%2147483647,(x.c0.b.val*s.val)%2147483647),
        ((x.c1.a.val*s.val)%2147483647,(x.c1.b.val*s.val)%2147483647)) := by
  obtain ⟨a,ha,ca,va⟩ := cm_m31 x.c0 s
  obtain ⟨b,hb,cb,vb⟩ := cm_m31 x.c1 s
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.QM31.mul_m31,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

#print axioms cm_m31
#print axioms qm_m31
end AspisR1.LPi_MixedValues

import NEB_WideCalls
import NEB_ByRCalls
set_option autoImplicit false
namespace NEB_AdditiveCalls
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem wide_add (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ a b,
      FIo_Native.aspis_core.field.QM31.add x.c0 y.c0 = ok a ∧ canonQ a ∧
      FIo_Native.aspis_core.field.QM31.add x.c1 y.c1 = ok b ∧ canonQ b ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.add x y = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,ca,_⟩ := LPi_TowerValues.qm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,_⟩ := LPi_TowerValues.qm_add x.c1 y.c1 hx.2 hy.2
  exact ⟨a,b,ha,ca,hb,cb,by simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,ha,hb,bind_tc_ok]⟩

theorem qm_scale (x : NQ) (s : U32) :
    ∃ a b,
      FIo_Native.aspis_core.field.CM31.mul_m31 x.c0 s = ok a ∧ canonC a ∧
      FIo_Native.aspis_core.field.CM31.mul_m31 x.c1 s = ok b ∧ canonC b ∧
      FIo_Native.aspis_core.field.QM31.mul_m31 x s = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,ca,_⟩ := LPi_MixedValues.cm_m31 x.c0 s
  obtain ⟨b,hb,cb,_⟩ := LPi_MixedValues.cm_m31 x.c1 s
  exact ⟨a,b,ha,ca,hb,cb,by simp only [FIo_Native.aspis_core.field.QM31.mul_m31,ha,hb,bind_tc_ok]⟩

/-- Both double callers pass the same canonical value twice. -/
theorem double_arguments (x : NC) (hx : canonC x) :
    canonC x ∧ canonC x ∧
    FIo_Native.aspis_core.field.CM31.double x = FIo_Native.aspis_core.field.CM31.add x x :=
  ⟨hx,hx,rfl⟩

theorem base_double_arguments (x : U32) (hx : x.val<2147483647) :
    x.val<2147483647 ∧ x.val<2147483647 ∧
    FIo_Native.aspis_core.field.M31.double x = FIo_Native.aspis_core.field.M31.add x x :=
  ⟨hx,hx,rfl⟩

#print axioms wide_add
#print axioms qm_scale
#print axioms double_arguments
#print axioms base_double_arguments
end NEB_AdditiveCalls

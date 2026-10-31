import NBG_FieldDischarge
set_option autoImplicit false
namespace NEB_FieldDomains
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- Projection is the actual argument expression in CM31.add/sub/mul. -/
theorem cm_arguments (x y : NC) (hx : canonC x) (hy : canonC y) :
    x.a.val < 2147483647 ∧ y.a.val < 2147483647 ∧
    x.b.val < 2147483647 ∧ y.b.val < 2147483647 :=
  ⟨hx.1,hy.1,hx.2,hy.2⟩

/-- Two same-input calls, in source order, returning canonical carriers. -/
theorem cm_add_calls (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ a b,
      FIo_Native.aspis_core.field.M31.add x.a y.a = ok a ∧
      FIo_Native.aspis_core.field.M31.add x.b y.b = ok b ∧
      a.val < 2147483647 ∧ b.val < 2147483647 ∧
      FIo_Native.aspis_core.field.CM31.add x y = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,_,ca⟩ := LPi_NatBase.add x.a y.a hx.1 hy.1
  obtain ⟨b,hb,_,cb⟩ := LPi_NatBase.add x.b y.b hx.2 hy.2
  exact ⟨a,b,ha,hb,ca,cb,by simp only [FIo_Native.aspis_core.field.CM31.add,ha,hb,bind_tc_ok]⟩

theorem cm_sub_calls (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ a b,
      FIo_Native.aspis_core.field.M31.sub x.a y.a = ok a ∧
      FIo_Native.aspis_core.field.M31.sub x.b y.b = ok b ∧
      a.val < 2147483647 ∧ b.val < 2147483647 ∧
      FIo_Native.aspis_core.field.CM31.sub x y = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,_,ca⟩ := LPi_NatBase.sub x.a y.a hx.1 hy.1
  obtain ⟨b,hb,_,cb⟩ := LPi_NatBase.sub x.b y.b hx.2 hy.2
  exact ⟨a,b,ha,hb,ca,cb,by simp only [FIo_Native.aspis_core.field.CM31.sub,ha,hb,bind_tc_ok]⟩

theorem qm_arguments (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    canonC x.c0 ∧ canonC y.c0 ∧ canonC x.c1 ∧ canonC y.c1 :=
  ⟨hx.1,hy.1,hx.2,hy.2⟩

theorem wide_arguments (x y : NE) (hx : canonE x) (hy : canonE y) :
    canonQ x.c0 ∧ canonQ y.c0 ∧ canonQ x.c1 ∧ canonQ y.c1 :=
  ⟨hx.1,hy.1,hx.2,hy.2⟩

/-- An earlier addition's returned carrier establishes the later product's
input domain. The result is selected by the actual emitted call. -/
theorem cm_cross_arguments (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ a b,
      FIo_Native.aspis_core.field.CM31.add x y = ok a ∧ canonC a ∧
      FIo_Native.aspis_core.field.CM31.mul a x = ok b ∧ canonC b := by
  obtain ⟨a,ha,ca,_⟩ := cm_add x y hx hy
  obtain ⟨b,hb,cb,_⟩ := cm_mul a x ca hx
  exact ⟨a,b,ha,ca,hb,cb⟩

#print axioms cm_arguments
#print axioms cm_add_calls
#print axioms cm_sub_calls
#print axioms qm_arguments
#print axioms wide_arguments
#print axioms cm_cross_arguments
end NEB_FieldDomains

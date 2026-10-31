import NEB_FieldDomains
set_option autoImplicit false
namespace NEB_CMCalls
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem multiply (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ m0 m1 m2 a b c : U32,
      FIo_Native.aspis_core.field.M31.mul x.a y.a = ok m0 ∧ m0.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul x.b y.b = ok m1 ∧ m1.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.reduce_u64 (LPi_CMProduct.cross x y) = ok m2 ∧ m2.val < 2147483647 ∧
      (LPi_CMProduct.cross x y).val=(x.a.val+x.b.val)*(y.a.val+y.b.val) ∧
      FIo_Native.aspis_core.field.M31.sub m0 m1 = ok a ∧ a.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.sub m2 m0 = ok b ∧ b.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.sub b m1 = ok c ∧ c.val < 2147483647 ∧
      FIo_Native.aspis_core.field.CM31.mul x y = ok ⟨a,c⟩ := by
  obtain ⟨m0,h0,_,c0⟩ := LPf_BaseMultiply.source x.a y.a
  obtain ⟨m1,h1,_,c1⟩ := LPf_BaseMultiply.source x.b y.b
  obtain ⟨m2,h2,_,c2⟩ := LPf_CoreReduction.source (LPi_CMProduct.cross x y)
  have hr : FIo_Native.aspis_core.field.M31.reduce_u64 (LPi_CMProduct.cross x y) = ok m2 := by
    simp only [FIo_Native.aspis_core.field.M31.reduce_u64,h2,bind_tc_ok]
  obtain ⟨a,ha,_,ca⟩ := LPi_NatBase.sub m0 m1 c0 c1
  obtain ⟨b,hb,_,cb⟩ := LPi_NatBase.sub m2 m0 c2 c0
  obtain ⟨c,hc,_,cc⟩ := LPi_NatBase.sub b m1 cb c1
  refine ⟨m0,m1,m2,a,b,c,h0,c0,h1,c1,hr,c2,LPi_CMProduct.cross_value x y hx hy,ha,ca,hb,cb,hc,cc,?_⟩
  simp only [FIo_Native.aspis_core.field.CM31.mul,h0,h1,lift,bind_tc_ok]
  change (do let t ← FIo_Native.aspis_core.field.M31.reduce_u64 (LPi_CMProduct.cross x y)
             let a ← FIo_Native.aspis_core.field.M31.sub m0 m1
             let b ← FIo_Native.aspis_core.field.M31.sub t m0
             let c ← FIo_Native.aspis_core.field.M31.sub b m1
             ok (⟨a,c⟩ : NC)) = _
  simp only [hr,ha,hb,hc,bind_tc_ok]

/-- The mixed-product packet accepts raw words. No canonical precondition is
introduced at either component call. -/
theorem scale (x : NC) (s : U32) :
    ∃ a b,
      FIo_Native.aspis_core.field.M31.mul x.a s = ok a ∧ a.val < 2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul x.b s = ok b ∧ b.val < 2147483647 ∧
      FIo_Native.aspis_core.field.CM31.mul_m31 x s = ok ⟨a,b⟩ := by
  obtain ⟨a,ha,_,ca⟩ := LPf_BaseMultiply.source x.a s
  obtain ⟨b,hb,_,cb⟩ := LPf_BaseMultiply.source x.b s
  exact ⟨a,b,ha,ca,hb,cb,by
    simp only [FIo_Native.aspis_core.field.CM31.mul_m31,ha,hb,bind_tc_ok]⟩

#print axioms multiply
#print axioms scale
end NEB_CMCalls

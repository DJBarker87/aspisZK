import SAG_MScaleTotal
set_option autoImplicit false
namespace AspisR1.SAG_QScaleTotal
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof

theorem total (x : field.QM31) (scalar : field.M31) :
    ∃ out, field.QM31.mul_m31 x scalar = ok out := by
  obtain ⟨a,ha⟩ := SAG_MScaleTotal.total x.c0.a scalar
  obtain ⟨b,hb⟩ := SAG_MScaleTotal.total x.c0.b scalar
  obtain ⟨c,hc⟩ := SAG_MScaleTotal.total x.c1.a scalar
  obtain ⟨d,hd⟩ := SAG_MScaleTotal.total x.c1.b scalar
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,?_⟩
  simp only [field.QM31.mul_m31,field.CM31.mul_m31,ha,hb,hc,hd,bind_tc_ok]

#print axioms total
end AspisR1.SAG_QScaleTotal

import SAG_QScaleTotal
import SAG_UnrestrictedScale
set_option autoImplicit false
namespace AspisR1.SAG_WScaleTotal
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof

theorem total (x : E) (scalar : field.M31) :
    ∃ out, field.wide_exact.WideExact.mul_m31 x scalar = ok out := by
  have nz : field.P.val ≠ 0 := by norm_num [field.P]
  obtain ⟨reduced,remRun,_⟩ := WP.spec_imp_exists (UScalar.rem_spec scalar nz)
  obtain ⟨lo,hlo⟩ := SAG_QScaleTotal.total x.c0 reduced
  obtain ⟨hi,hhi⟩ := SAG_QScaleTotal.total x.c1 reduced
  exact ⟨⟨lo,hi⟩,by simp only [field.wide_exact.WideExact.mul_m31,remRun,hlo,hhi,bind_tc_ok]⟩

#print axioms total
end AspisR1.SAG_WScaleTotal

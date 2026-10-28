import R1Z.ProverCommitNativeNeg49
import R1Z.ProverCommitInterpolationInverse48
/-! Current complex inverse owner, with the norm's nonzero assertion discharged
from the literal extension field's rootlessness theorem. -/
set_option autoImplicit false
namespace R1Z.ProverCommitNativeCInverse49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitNativeC49
open AspisV8R15.ExactTowerBase

theorem norm_value (x : CM31Exact) : QuadraticAlgebra.norm x=x.re*x.re+x.im*x.im := by
  simp only [QuadraticAlgebra.norm_def]
  ring

theorem inverse (x : Old.C) (hx : Canonical x) (hn : value x≠0) :
    ∃ z : Old.C, kernels.inverse_c (source x)=ok (source z) ∧
      Canonical z ∧ value z=(value x)⁻¹ := by
  obtain ⟨aa,haa,hcaa,hvaa⟩ := ProverCommitM31Ops48.mul_exact x.a x.a
  obtain ⟨bb,hbb,hcbb,hvbb⟩ := ProverCommitM31Ops48.mul_exact x.b x.b
  obtain ⟨n,hnn,hcn,hvn⟩ := ProverCommitM31Ops48.add_exact aa bb hcaa hcbb
  have hnorm : ProverCommitM31Ops48.decode n=QuadraticAlgebra.norm (value x) := by
    rw [hvn,hvaa,hvbb,norm_value];rfl
  have nonzero : n≠0#u32 := by
    intro hz
    have h0 : ProverCommitM31Ops48.decode n=0 := by rw [hz];rfl
    apply hn
    apply QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp
    rw [←hnorm,h0]
  obtain ⟨ni,hni,hcni,hvni⟩ := ProverCommitInterpolationInverse48.inverse_exact n nonzero
  obtain ⟨a,ha,hca,hva⟩ := ProverCommitM31Ops48.mul_exact x.a ni
  obtain ⟨nb,hnb,hcnb,hvnb⟩ := ProverCommitNativeNeg49.neg_word x.b hx.2
  obtain ⟨b,hb,hcb,hvb⟩ := ProverCommitM31Ops48.mul_exact nb ni
  refine ⟨⟨a,b⟩,?_,⟨hca,hcb⟩,?_⟩
  · simp only [kernels.inverse_c,source,ProverCommitRelease47.convC,fromC,
      haa,hbb,hnn,hni,ha,hnb,hb,bind_tc_ok]
  · have hvi : ProverCommitM31Ops48.decode ni=(QuadraticAlgebra.norm (value x))⁻¹ := by
      change ProverCommitM31Ops48.decode ni=(ProverCommitM31Ops48.decode n)⁻¹ at hvni
      rw [hvni,hnorm]
    apply QuadraticAlgebra.ext
    · change ProverCommitM31Ops48.decode a=_
      rw [hva,hvi,QuadraticAlgebra.re_inv]
      simp only [zero_mul,add_zero]
      change (x.a.val : M31Exact)*(QuadraticAlgebra.norm (value x))⁻¹=(QuadraticAlgebra.norm (value x))⁻¹*(x.a.val : M31Exact)
      ring
    · change ProverCommitM31Ops48.decode b=_
      rw [hvb,hvi]
      change (nb.val : M31Exact)*(QuadraticAlgebra.norm (value x))⁻¹=_
      rw [hvnb,QuadraticAlgebra.im_inv]
      change -(x.b.val : M31Exact)*(QuadraticAlgebra.norm (value x))⁻¹= -((QuadraticAlgebra.norm (value x))⁻¹*(x.b.val : M31Exact))
      ring

#print axioms norm_value
#print axioms inverse
end R1Z.ProverCommitNativeCInverse49

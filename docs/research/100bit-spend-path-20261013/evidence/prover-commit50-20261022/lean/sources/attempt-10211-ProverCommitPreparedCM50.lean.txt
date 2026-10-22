import AspisR1ProducerRelease47.Prepared50
import R1Z.ProverCommitPrepare50
/-! Canonical prepared CM31 multiplication for any supplied row with the
three explicitly stated input-coordinate equations. -/
set_option autoImplicit false
namespace R1Z.ProverCommitPreparedCM50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisV8R15.ExactTowerBase
open ProverCommitChannelAlgebra49 (cmComponents)

theorem cm (a : Nat → U32) (x : CM31Exact) (y : Old.C)
    (hy : ProverCommitNativeC49.Canonical y)
    (ha : ∀ j : Fin 3, ((a j.val).val : M31Exact)=cmComponents x j) :
    ∃ z : Old.C, prepared50.cm (ProverCommitArray49.array 3#usize a) (ProverCommitNativeC49.source y)=ok (ProverCommitNativeC49.source z) ∧
      ProverCommitNativeC49.Canonical z ∧ ProverCommitNativeC49.value z=x*ProverCommitNativeC49.value y := by
  obtain ⟨s,hs,hcs,hvs⟩ := ProverCommitM31Ops48.add_exact y.a y.b hy.1 hy.2
  obtain ⟨m0,hm0,hc0,hv0⟩ := ProverCommitM31Ops48.mul_exact (a 0) y.a
  obtain ⟨m1,hm1,hc1,hv1⟩ := ProverCommitM31Ops48.mul_exact (a 1) y.b
  obtain ⟨m2,hm2,hc2,hv2⟩ := ProverCommitM31Ops48.mul_exact (a 2) s
  obtain ⟨r,hr,hcr,hvr⟩ := ProverCommitM31Ops48.sub_exact m0 m1 hc0 hc1
  obtain ⟨t,ht,hct,hvt⟩ := ProverCommitM31Ops48.sub_exact m2 m0 hc2 hc0
  obtain ⟨i,hi,hci,hvi⟩ := ProverCommitM31Ops48.sub_exact t m1 hct hc1
  have h0 : ((a 0).val : M31Exact)=x.re := ha 0
  have h1 : ((a 1).val : M31Exact)=x.im := ha 1
  have h2 : ((a 2).val : M31Exact)=x.re+x.im := ha 2
  refine ⟨⟨r,i⟩,?_,⟨hcr,hci⟩,?_⟩
  · simp only [prepared50.cm,
      ProverCommitArray49.index 3#usize _ 0#usize (by decide),
      ProverCommitArray49.index 3#usize _ 1#usize (by decide),
      ProverCommitArray49.index 3#usize _ 2#usize (by decide),
      show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,show (2#usize).val=2 from rfl,
      ProverCommitNativeC49.source,ProverCommitRelease47.convC,fromC,
      hm0,hm1,hm2,hs,hr,ht,hi,bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · change (r.val : M31Exact)=(x*ProverCommitNativeC49.value y).re
      change (r.val : M31Exact)=(m0.val : M31Exact)-(m1.val : M31Exact) at hvr
      change (m0.val : M31Exact)=((a 0).val : M31Exact)*(y.a.val : M31Exact) at hv0
      change (m1.val : M31Exact)=((a 1).val : M31Exact)*(y.b.val : M31Exact) at hv1
      rw [hvr,hv0,hv1,h0,h1]
      simp [QuadraticAlgebra.re_mul,ProverCommitNativeC49.value,ProverCommitMulU48.decodeC]
      <;> ring
    · change (i.val : M31Exact)=(x*ProverCommitNativeC49.value y).im
      change (i.val : M31Exact)=(t.val : M31Exact)-(m1.val : M31Exact) at hvi
      change (t.val : M31Exact)=(m2.val : M31Exact)-(m0.val : M31Exact) at hvt
      change (m0.val : M31Exact)=((a 0).val : M31Exact)*(y.a.val : M31Exact) at hv0
      change (m1.val : M31Exact)=((a 1).val : M31Exact)*(y.b.val : M31Exact) at hv1
      change (m2.val : M31Exact)=((a 2).val : M31Exact)*(s.val : M31Exact) at hv2
      change (s.val : M31Exact)=(y.a.val : M31Exact)+(y.b.val : M31Exact) at hvs
      rw [hvi,hvt,hv2,hv0,hv1,hvs,h0,h1,h2]
      simp [QuadraticAlgebra.im_mul,ProverCommitNativeC49.value,ProverCommitMulU48.decodeC]
      <;> ring

#print axioms cm
end R1Z.ProverCommitPreparedCM50

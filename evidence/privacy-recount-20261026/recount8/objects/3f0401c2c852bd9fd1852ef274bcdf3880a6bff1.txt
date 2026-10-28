import R1Z.ProverCommitNativeCInverse49
import R1Z.ProverCommitNativeQSquare49
/-! Complete native quadratic inverse owner, including its zero rejection. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitNativeQInverse49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisV8R15.ExactTowerBase
open AspisR1.ExtractedCurrentQM31Exact (decode)
local instance : DecidableEq Old.Q := Classical.decEq _

theorem zero_test (x : Old.Q) :
    field.QM31.is_zero (ProverCommitNativeQ48.source x)=ok (decide (x=zero)) := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  by_cases ha : a=0#u32 <;> by_cases hb : b=0#u32 <;>
    by_cases hc : c=0#u32 <;> by_cases hd : d=0#u32 <;>
    simp [field.QM31.is_zero,field.CM31.is_zero,field.M31.is_zero,
      ProverCommitNativeQ48.source,ProverCommitRelease47.convQ,ProverCommitRelease47.convC,
      fromQ,fromC,zero,ha,hb,hc,hd]

theorem zero_iff (x : Old.Q) (hx : Canonical x) : decode x=0 ↔ x=zero := by
  rw [←zero_decode]
  exact AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff x zero hx zero_canonical

theorem norm_value (x : QM31Exact) :
    QuadraticAlgebra.norm x=x.re*x.re-qm31R*x.im*x.im := by
  simp only [QuadraticAlgebra.norm_def]
  ring

theorem inverse (x : Old.Q) (hx : Canonical x) (hn : decode x≠0) :
    ∃ z : Old.Q, kernels.inverse_q (ProverCommitNativeQ48.source x)=ok (some (ProverCommitNativeQ48.source z)) ∧
      Canonical z ∧ decode z=(decode x)⁻¹ := by
  have nz : x≠zero := by intro he;apply hn;rw [he,zero_decode]
  obtain ⟨a,ha,hca,hva⟩ := ProverCommitNativeSquare49.square x.c0 hx.1
  obtain ⟨b,hb,hcb,hvb⟩ := ProverCommitNativeSquare49.square x.c1 hx.2
  obtain ⟨r,hr,hcr,hvr⟩ := ProverCommitNativeC49.mul_r b hcb
  have hr' : kernels.mul_r (ProverCommitNativeC49.source b)=ok (ProverCommitNativeC49.source r) := hr
  obtain ⟨n,hnn,hcn,hvn⟩ := ProverCommitNativeC49.sub a r hca hcr
  have hnorm : ProverCommitNativeC49.value n=QuadraticAlgebra.norm (decode x) := by
    rw [hvn,hva,hvr,hvb,norm_value]
    change ProverCommitNativeC49.value x.c0*ProverCommitNativeC49.value x.c0-qm31R*(ProverCommitNativeC49.value x.c1*ProverCommitNativeC49.value x.c1)=ProverCommitNativeC49.value x.c0*ProverCommitNativeC49.value x.c0-qm31R*ProverCommitNativeC49.value x.c1*ProverCommitNativeC49.value x.c1
    ring
  have nonzero : ProverCommitNativeC49.value n≠0 := by
    intro he;apply hn
    exact QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp (hnorm.symm.trans he)
  obtain ⟨ni,hni,hcni,hvni⟩ := ProverCommitNativeCInverse49.inverse n hcn nonzero
  obtain ⟨lo,hlo,hclo,hvlo⟩ := ProverCommitNativeC49.mul x.c0 ni hx.1 hcni
  obtain ⟨nb,hnb,hcnb,hvnb⟩ := ProverCommitNativeNeg49.neg x.c1 hx.2
  obtain ⟨hi,hhi,hchi,hvhi⟩ := ProverCommitNativeC49.mul nb ni hcnb hcni
  refine ⟨⟨lo,hi⟩,?_,⟨hclo,hchi⟩,?_⟩
  · rw [kernels.inverse_q,zero_test]
    simp only [nz,decide_false,Bool.false_eq_true,if_false,bind_tc_ok]
    change (do
      let a ← field.CM31.square (ProverCommitNativeC49.source x.c0)
      let b ← field.CM31.square (ProverCommitNativeC49.source x.c1)
      let r ← kernels.mul_r b
      let n ← field.CM31.sub a r
      let ni ← kernels.inverse_c n
      let lo ← field.CM31.mul (ProverCommitNativeC49.source x.c0) ni
      let nb ← field.CM31.neg (ProverCommitNativeC49.source x.c1)
      let hi ← field.CM31.mul nb ni
      ok (some ({c0:=lo,c1:=hi} : field.QM31)))=ok _
    simp only [ha,hb,hr',hnn,hni,hlo,hnb,hhi,bind_tc_ok]
    rfl
  · rw [hnorm] at hvni
    apply QuadraticAlgebra.ext
    · change ProverCommitNativeC49.value lo=_
      rw [hvlo,hvni,QuadraticAlgebra.re_inv]
      simp only [zero_mul,add_zero]
      change ProverCommitNativeC49.value x.c0*(QuadraticAlgebra.norm (decode x))⁻¹=(QuadraticAlgebra.norm (decode x))⁻¹*ProverCommitNativeC49.value x.c0
      ring
    · change ProverCommitNativeC49.value hi=_
      rw [hvhi,hvnb,hvni,QuadraticAlgebra.im_inv]
      change -ProverCommitNativeC49.value x.c1*(QuadraticAlgebra.norm (decode x))⁻¹= -((QuadraticAlgebra.norm (decode x))⁻¹*ProverCommitNativeC49.value x.c1)
      ring

theorem reject_zero : kernels.inverse_q (ProverCommitNativeQ48.source zero)=ok none := by
  rw [kernels.inverse_q,zero_test]
  simp

#print axioms zero_test
#print axioms zero_iff
#print axioms norm_value
#print axioms inverse
#print axioms reject_zero
end R1Z.ProverCommitNativeQInverse49

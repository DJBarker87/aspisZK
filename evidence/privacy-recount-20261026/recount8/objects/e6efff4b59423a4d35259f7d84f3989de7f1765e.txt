import AspisR1ProducerRelease47.Linear50
import R1Z.ProverCommitM31Ops48
import R1Z.ProverCommitNativeQ48
/-! Actual four-limb QM31 base-field scaling. Raw scalar inputs are arbitrary. -/
set_option autoImplicit false
namespace R1Z.ProverCommitScale50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

theorem scale (x : Old.Q) (s : U32) :
    ∃ z : Old.Q, field.QM31.mul_m31 (ProverCommitNativeQ48.source x) s=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=decode x*(s.val:QM31Exact) := by
  obtain ⟨a,ha,hca,hda⟩ := ProverCommitM31Ops48.mul_exact x.c0.a s
  obtain ⟨b,hb,hcb,hdb⟩ := ProverCommitM31Ops48.mul_exact x.c0.b s
  obtain ⟨c,hc,hcc,hdc⟩ := ProverCommitM31Ops48.mul_exact x.c1.a s
  obtain ⟨d,hd,hcd,hdd⟩ := ProverCommitM31Ops48.mul_exact x.c1.b s
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,?_,⟨⟨hca,hcb⟩,⟨hcc,hcd⟩⟩,?_⟩
  · simp only [field.QM31.mul_m31,field.CM31.mul_m31,ProverCommitNativeQ48.source,
      ProverCommitRelease47.convQ,ProverCommitRelease47.convC,fromQ,fromC,ha,hb,hc,hd,bind_tc_ok]
  · apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,QuadraticAlgebra.re_natCast,
        QuadraticAlgebra.im_natCast,mul_zero,zero_mul,add_zero,zero_add] <;>
      apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,QuadraticAlgebra.re_natCast,
        QuadraticAlgebra.im_natCast,mul_zero,zero_mul,add_zero,zero_add]
    · exact hda
    · exact hdb
    · exact hdc
    · exact hdd

#print axioms scale
end R1Z.ProverCommitScale50

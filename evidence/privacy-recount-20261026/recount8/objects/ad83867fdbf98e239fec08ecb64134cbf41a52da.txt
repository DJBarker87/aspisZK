import R1Z.ProverCommitNativeSquare49
import R1Z.ProverCommitNativeQ48
/-! Complete current QM31 square over arbitrary canonical tower inputs. -/
set_option autoImplicit false
namespace R1Z.ProverCommitNativeQSquare49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisV8R15.ExactTowerBase
open AspisR1.ExtractedCurrentQM31Exact (decode)

theorem square (x : Old.Q) (hx : Canonical x) :
    ∃ z : Old.Q, field.QM31.square (ProverCommitNativeQ48.source x)=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=decode x*decode x := by
  obtain ⟨a,ha,hca,hva⟩ := ProverCommitNativeSquare49.square x.c0 hx.1
  obtain ⟨b,hb,hcb,hvb⟩ := ProverCommitNativeSquare49.square x.c1 hx.2
  obtain ⟨r,hr,hcr,hvr⟩ := ProverCommitNativeC49.mul_r b hcb
  obtain ⟨lo,hlo,hclo,hvlo⟩ := ProverCommitNativeC49.add a r hca hcr
  obtain ⟨ab,hab,hcab,hvab⟩ := ProverCommitNativeC49.mul x.c0 x.c1 hx.1 hx.2
  obtain ⟨hi,hhi,hchi,hvhi⟩ := ProverCommitNativeC49.add ab ab hcab hcab
  refine ⟨⟨lo,hi⟩,?_,⟨hclo,hchi⟩,?_⟩
  · change (do
      let a ← field.CM31.square (ProverCommitNativeC49.source x.c0)
      let b ← field.CM31.square (ProverCommitNativeC49.source x.c1)
      let r ← field.mul_by_r b
      let lo ← field.CM31.add a r
      let ab ← field.CM31.mul (ProverCommitNativeC49.source x.c0) (ProverCommitNativeC49.source x.c1)
      let hi ← field.CM31.double ab
      ok ({c0:=lo,c1:=hi} : field.QM31))=ok _
    simp only [ha,hb,hr,hlo,hab,field.CM31.double,hhi,bind_tc_ok]
    rfl
  · apply QuadraticAlgebra.ext
    · change ProverCommitNativeC49.value lo=ProverCommitNativeC49.value x.c0*ProverCommitNativeC49.value x.c0+qm31R*ProverCommitNativeC49.value x.c1*ProverCommitNativeC49.value x.c1
      rw [hvlo,hva,hvr,hvb];ring
    · simp only [QuadraticAlgebra.im_mul]
      change ProverCommitNativeC49.value hi=ProverCommitNativeC49.value x.c0*ProverCommitNativeC49.value x.c1+ProverCommitNativeC49.value x.c1*ProverCommitNativeC49.value x.c0+0*ProverCommitNativeC49.value x.c1*ProverCommitNativeC49.value x.c1
      rw [hvhi,hvab];ring

#print axioms square
end R1Z.ProverCommitNativeQSquare49

import R1Z.ProverCommitWideOps48
/-! Source subtraction on all eight canonical limbs, including nonzero high
coordinates. -/
set_option autoImplicit false
namespace R1Z.ProverCommitWideSub53
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitWideOps48
open AspisR1.ExtractedCurrentQM31Exact (decode)

theorem sub_exact (x y : Raw) (hx : canonical x) (hy : canonical y) :
    ∃ z : Raw, field.wide_exact.WideExact.sub (source x) (source y)=ok (source z) ∧
      canonical z ∧ value z=value x-value y := by
  obtain ⟨lo,hlo,hclo,hdlo⟩ := ProverCommitSubtraction47.qsub_checked x.1 y.1 hx.1 hy.1
  obtain ⟨hi,hhi,hchi,hdhi⟩ := ProverCommitSubtraction47.qsub_checked x.2 y.2 hx.2 hy.2
  have low := ProverCommitRelease47.subQ _ _ _ hlo
  have high := ProverCommitRelease47.subQ _ _ _ hhi
  refine ⟨(lo,hi),?_,⟨hclo,hchi⟩,?_⟩
  · unfold field.wide_exact.WideExact.sub source pack ProverCommitRelease47.convE
    rw [low,high]
    rfl
  · apply QuadraticAlgebra.ext
    · exact hdlo
    · exact hdhi

#print axioms sub_exact
end R1Z.ProverCommitWideSub53

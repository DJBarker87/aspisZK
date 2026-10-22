import R1Z.ProverCommitTerminalEquality51
import R1Z.ProverCommitSampleTail49
/-! The complete terminal arithmetic suffix, with its actual field calls. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTerminalSuffix51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitSubtraction47 (one one_canonical one_decode)
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
attribute [local irreducible] ProverCommitNativeQ48.source

theorem exact_result (eq composition h1 active mu : Old.Q)
    (heq : Canonical eq) (hcomp : Canonical composition) (hh1 : Canonical h1)
    (hactive : Canonical active) (hmu : Canonical mu) :
    ∃ z : Old.Q, terminal_eq51.suffix (ProverCommitNativeQ48.source eq) (ProverCommitNativeQ48.source composition)
      (ProverCommitNativeQ48.source h1) (ProverCommitNativeQ48.source active) (ProverCommitNativeQ48.source mu)=
        ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=decode eq*decode composition+decode mu*decode h1+
        (decode mu*decode mu)*((1-decode active)*decode h1) := by
  obtain ⟨q,hq,hcq,hdq⟩ := ProverCommitNativeQ48.mul eq composition heq hcomp
  obtain ⟨q1,hq1,hcq1,hdq1⟩ := ProverCommitNativeQ48.mul mu h1 hmu hh1
  obtain ⟨q2,hq2,hcq2,hdq2⟩ := ProverCommitNativeQ48.add q q1 hcq hcq1
  obtain ⟨q3,hq3,hcq3,hdq3⟩ := ProverCommitNativeQ48.mul mu mu hmu hmu
  obtain ⟨q4,hq4,hcq4,hdq4⟩ := ProverCommitNativeQ48.sub one active one_canonical hactive
  obtain ⟨q5,hq5,hcq5,hdq5⟩ := ProverCommitNativeQ48.mul q4 h1 hcq4 hh1
  obtain ⟨q6,hq6,hcq6,hdq6⟩ := ProverCommitNativeQ48.mul q3 q5 hcq3 hcq5
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitNativeQ48.add q2 q6 hcq2 hcq6
  refine ⟨z,?_,hcz,?_⟩
  · simp only [terminal_eq51.suffix,ProverCommitSampleTail49.source_one,hq,hq1,hq2,hq3,hq4,hq5,hq6,hz,bind_tc_ok]
  · rw [hdz,hdq2,hdq,hdq1,hdq6,hdq3,hdq5,hdq4,one_decode]

#print axioms exact_result
end R1Z.ProverCommitTerminalSuffix51

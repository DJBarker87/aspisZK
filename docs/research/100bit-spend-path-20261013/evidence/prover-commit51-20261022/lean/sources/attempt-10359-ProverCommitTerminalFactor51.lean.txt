import AspisR1ProducerRelease47.TerminalEq51
import R1Z.ProverCommitNativeQ48
import R1Z.ProverCommitSampleTail49
import R1Z.ProverCommitTerminalMath51
/-! All five native field calls in a terminal equality factor. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTerminalFactor51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitSubtraction47 (one one_canonical one_decode)
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
attribute [local irreducible] ProverCommitNativeQ48.source

theorem exact_result (a b : Old.Q) (ha : Canonical a) (hb : Canonical b) :
    ∃ z : Old.Q, terminal_eq51.factor (ProverCommitNativeQ48.source a) (ProverCommitNativeQ48.source b)=
      ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=ProverCommitTerminalMath51.factor (decode a) (decode b) := by
  obtain ⟨ab,hab,hcab,hdab⟩ := ProverCommitNativeQ48.mul a b ha hb
  obtain ⟨q,hq,hcq,hdq⟩ := ProverCommitNativeQ48.sub one a one_canonical ha
  obtain ⟨q1,hq1,hcq1,hdq1⟩ := ProverCommitNativeQ48.sub q b hcq hb
  obtain ⟨q2,hq2,hcq2,hdq2⟩ := ProverCommitNativeQ48.add q1 ab hcq1 hcab
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitNativeQ48.add q2 ab hcq2 hcab
  refine ⟨z,?_,hcz,?_⟩
  · simp only [terminal_eq51.factor,ProverCommitSampleTail49.source_one,hab,hq,hq1,hq2,hz,bind_tc_ok]
  · rw [hdz,hdq2,hdq1,hdq,hdab,one_decode]
    rfl

#print axioms exact_result
end R1Z.ProverCommitTerminalFactor51

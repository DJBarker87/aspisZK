import R1Z.ProverCommitQOps48
/-! Direct canonical QM31 source arithmetic, for the semantic producer rather
than only the embedded WideExact evaluator. -/
set_option autoImplicit false
namespace R1Z.ProverCommitNativeQ48
open Aeneas Aeneas.Std Result ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitRelease47
open AspisR1.ExtractedCurrentQM31Exact (decode)
abbrev Q := AspisR1ProducerRelease47.field.QM31

def source (x : Old.Q) : Q := convQ (fromQ x)

theorem add (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q, AspisR1ProducerRelease47.field.QM31.add (source x) (source y)=ok (source z) ∧
      Canonical z ∧ decode z=decode x+decode y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitQOps48.add x y hx hy
  exact ⟨z,ProverCommitRelease47.addQ _ _ _ hz,hc,hd⟩

theorem mul (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q, AspisR1ProducerRelease47.field.QM31.mul (source x) (source y)=ok (source z) ∧
      Canonical z ∧ decode z=decode x*decode y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitQOps48.mul x y hx hy
  exact ⟨z,ProverCommitRelease47.mulQ _ _ _ hz,hc,hd⟩

theorem sub (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q, AspisR1ProducerRelease47.field.QM31.sub (source x) (source y)=ok (source z) ∧
      Canonical z ∧ decode z=decode x-decode y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitSubtraction47.qsub_checked x y hx hy
  exact ⟨z,ProverCommitRelease47.subQ _ _ _ hz,hc,hd⟩

#print axioms add
#print axioms mul
#print axioms sub
end R1Z.ProverCommitNativeQ48

import R1Z.ProverRwDictionaryScalar
import R1Z.ProverCommitNativeQ48
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryCorrectQMul
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
variable [ExternalTypes]
abbrev input (x : Old.Q) : ProverRwDictionaryTower.Q :=
  ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source x)

/-- Canonical operands; no supplied success or operation/model equation. -/
theorem correct (ops : ExternalFuns) (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q,
      (ProverRwDictionaryScalar.selected ops).op69 (input x) (input y) = .ok (input z) ∧
      Canonical z ∧ decode z = decode x * decode y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitNativeQ48.mul x y hx hy
  refine ⟨z,?_,hc,hd⟩
  have entry : (ProverRwDictionaryScalar.selected ops).op69 = ProverRwDictionaryTower.qMul := rfl
  rw [entry]
  unfold ProverRwDictionaryTower.qMul input
  rw [ProverRwDictionaryTower.native_q_roundtrip,ProverRwDictionaryTower.native_q_roundtrip,hz]
  rfl

#print axioms correct
end R1Z.ProverRwDictionaryCorrectQMul

import R1Z.ProverCommitInverseCases51
import R1Z.ProverCommitHalf49
/-! Exact half-inverse prefix shared by the emitter and final semantic shift. -/
set_option autoImplicit false
namespace R1Z.ProverCommitHalfPrefix51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

def run (a : field.QM31) : Result (Option field.QM31) := do
  let half ← extras.half
  let denominator ← field.QM31.sub a half
  kernels.inverse_q denominator

attribute [local irreducible] ProverCommitNativeQ48.source ProverCommitHalf49.raw

theorem none_iff (a : Old.Q) (ha : Canonical a) :
    run (ProverCommitNativeQ48.source a)=ok none ↔ decode a=(2 : QM31Exact)⁻¹ := by
  obtain ⟨d,hd,hcd,hvd⟩ := ProverCommitNativeQ48.sub a ProverCommitHalf49.raw ha ProverCommitHalf49.canonical
  rw [run,ProverCommitHalf49.result]
  simp only [bind_tc_ok,hd]
  rw [ProverCommitInverseCases51.none_iff d hcd,hvd,ProverCommitHalf49.value,sub_eq_zero]

theorem some_nonhalf (a : Old.Q) (ha : Canonical a) (i : field.QM31)
    (hs : run (ProverCommitNativeQ48.source a)=ok (some i)) : decode a≠(2 : QM31Exact)⁻¹ := by
  intro he
  rw [(none_iff a ha).mpr he] at hs
  cases hs

theorem inverse (a : Old.Q) (ha : Canonical a) (hne : decode a≠(2 : QM31Exact)⁻¹) :
    ∃ i : Old.Q, run (ProverCommitNativeQ48.source a)=ok (some (ProverCommitNativeQ48.source i)) ∧
      Canonical i ∧ decode i=(decode a-(2 : QM31Exact)⁻¹)⁻¹ := by
  obtain ⟨d,hd,hcd,hvd⟩ := ProverCommitNativeQ48.sub a ProverCommitHalf49.raw ha ProverCommitHalf49.canonical
  have hn : decode d≠0 := by rw [hvd,ProverCommitHalf49.value];exact sub_ne_zero.mpr hne
  obtain ⟨i,hi,hci,hvi⟩ := ProverCommitNativeQInverse49.inverse d hcd hn
  refine ⟨i,?_,hci,?_⟩
  · simp only [run,ProverCommitHalf49.result,hd,hi,bind_tc_ok]
  · rw [hvi,hvd,ProverCommitHalf49.value]

#print axioms none_iff
#print axioms some_nonhalf
#print axioms inverse
end R1Z.ProverCommitHalfPrefix51

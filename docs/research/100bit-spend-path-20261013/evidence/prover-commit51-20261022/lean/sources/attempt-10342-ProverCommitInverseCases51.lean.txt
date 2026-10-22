import R1Z.ProverCommitNativeQInverse49
/-! Both inverse branches; a successful Some answer forces a nonzero input. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitInverseCases51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

theorem zero_reject (x : Old.Q) (hx : Canonical x) (hz : decode x=0) :
    kernels.inverse_q (ProverCommitNativeQ48.source x)=ok none := by
  have he := (ProverCommitNativeQInverse49.zero_iff x hx).mp hz
  rw [kernels.inverse_q,ProverCommitNativeQInverse49.zero_test]
  simp only [he,decide_true,if_true,bind_tc_ok]

theorem some_nonzero (x : Old.Q) (hx : Canonical x) (z : field.QM31)
    (hs : kernels.inverse_q (ProverCommitNativeQ48.source x)=ok (some z)) : decode x≠0 := by
  intro hzero
  rw [zero_reject x hx hzero] at hs
  cases hs

theorem none_iff (x : Old.Q) (hx : Canonical x) :
    kernels.inverse_q (ProverCommitNativeQ48.source x)=ok none ↔ decode x=0 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨z,hz,_,_⟩ := ProverCommitNativeQInverse49.inverse x hx hn
    rw [h] at hz
    cases hz
  · exact zero_reject x hx

#print axioms zero_reject
#print axioms some_nonzero
#print axioms none_iff
end R1Z.ProverCommitInverseCases51

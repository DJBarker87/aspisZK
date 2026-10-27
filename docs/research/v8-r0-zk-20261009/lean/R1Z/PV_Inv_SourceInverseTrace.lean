import R1Z.PV_Inv_SourceBranch
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_SourceInverseTrace
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitNativeQ48 (source)
open AspisR1.ExtractedCurrentQM31Exact (decode)

def observedInverse (chi slot : Old.Q) : Result (Bool × Option field.QM31) := do
  let d ← field.QM31.sub (source chi) (source slot)
  let b ← field.QM31.is_zero d
  let inv ← kernels.inverse_q d
  ok (b,inv)

theorem success (chi slot : Old.Q) (hc : Canonical chi) (hs : Canonical slot)
    (hn : decode chi ≠ decode slot) :
    ∃ inv : Old.Q, Canonical inv ∧ observedInverse chi slot=ok (false,some (source inv)) := by
  obtain ⟨d,inv,hsub,hcan,hnon,htest,hinv,hci⟩ := PV_Inv_NativeQ.subtract_nonzero chi slot hc hs hn
  refine ⟨inv,hci,?_⟩
  simp only [observedInverse,hsub,htest,hinv,bind_tc_ok]

#print axioms success
end R1Z.PV_Inv_SourceInverseTrace

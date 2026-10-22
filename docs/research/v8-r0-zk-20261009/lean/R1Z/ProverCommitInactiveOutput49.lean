import R1Z.ProverCommitInactiveModel49
/-! The native inactive-kind Bool branch and canonical literal field result. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitInactiveOutput49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitInactiveModel49
open ProverCommitPrimitive47 ProverCommitSubfieldOps47

def run (j : Usize) : Result field.QM31 := do
  let inactive ← AspisR1InactiveOwner49.owned.inactive j
  ok (if inactive then field.QM31.ONE else field.QM31.ZERO)

theorem exact_result (j : Usize) (hj : j.val<1024) :
    run j=ok (ProverCommitNativeQ48.source (raw j)) ∧ Canonical (raw j) ∧
      AspisR1.ExtractedCurrentQM31Exact.decode (raw j)=AspisR0.Opening.indicator R0P.copyInactiveRows
        (AspisR1.rowEquiv.symm ⟨j.val,hj⟩) := by
  refine ⟨?_,raw_canonical j,raw_value j hj⟩
  rw [run,inactive_exact]
  simp only [bind_tc_ok]
  by_cases h : row j ∈ R0P.copyInactiveRows
  · simp only [h,decide_true,if_true,raw,ProverCommitSampleTail49.source_one]
  · simp only [h,decide_false,Bool.false_eq_true,if_false,raw,ProverCommitQArray48.source_zero]

#print axioms exact_result
end R1Z.ProverCommitInactiveOutput49

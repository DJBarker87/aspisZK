import R1Z.PV_Inv_NativeQ
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_SourceBranch
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitNativeQ48 (source)
open AspisR1.ExtractedCurrentQM31Exact (decode)

def branch (chi slot : Old.Q) : Result Bool := do
  let d ← field.QM31.sub (source chi) (source slot)
  field.QM31.is_zero d

theorem branch_false (chi slot : Old.Q) (hc : Canonical chi) (hs : Canonical slot)
    (hn : decode chi ≠ decode slot) : branch chi slot = ok false := by
  obtain ⟨d,inv,hsub,hcan,hnon,htest,hinv,hci⟩ := PV_Inv_NativeQ.subtract_nonzero chi slot hc hs hn
  simp only [branch,hsub,bind_tc_ok,htest]

#print axioms branch_false
end R1Z.PV_Inv_SourceBranch

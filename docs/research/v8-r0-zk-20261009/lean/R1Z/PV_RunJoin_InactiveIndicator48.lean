import R1Z.PV_RunJoin_InactiveCell48
import R1Z.ProverCommitInactiveModel49
import R1Z.ProverCommitWideQM31Scalar49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InactiveIndicator48
open Aeneas Aeneas.Std Result
open ProverCommitWideOps48 (Exact)

def mask (j : Nat) : Exact :=
  if h : j<1024 then ProverCommitWideQM31Scalar49.embed
    (AspisR0.Opening.indicator R0P.copyInactiveRows (AspisR1.rowEquiv.symm ⟨j,h⟩)) else 0

theorem complete (j : Usize) (hj : j.val<1024) :
    ProverCommitWideQM31Scalar49.embed
      (AspisR1.ExtractedCurrentQM31Exact.decode (ProverCommitInactiveModel49.raw j))=mask j.val := by
  rw [mask,dif_pos hj,ProverCommitInactiveModel49.raw_value j hj]
#print axioms complete
end R1Z.PV_RunJoin_InactiveIndicator48

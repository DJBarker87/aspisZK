import NNH_CommonResumeDomain
set_option autoImplicit false
namespace NNH_ResumeDigest
open Aeneas Aeneas.Std AspisR1 VTop_Stages

theorem same {H : Type} (d : aspis_core.digest.Digest32 H) :
 NJC_ResumeCalls.digest d=VTop_Checkpoint.digest d := by
 cases d
 rfl
#print axioms same
end NNH_ResumeDigest

import XRk_Tx1Projection
import XRk_DotProjection
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRk_Tx1Association
theorem candidateTx1AcceptedPath : XRk_Association.CandidateTx1AcceptedPath := by
  intro H D pub physical proof split hash obs bytes run
  obtain ⟨p,scratch,zero,a,hzero,hprepare,hsplit,hpowers,_⟩ :=
    XRk_Tx1Projection.cuts D pub physical proof split hash obs bytes run
  exact ⟨p,scratch,zero,hzero,hprepare,hsplit,hpowers⟩
theorem acceptedCandidateCheckpoint : XRk_Association.AcceptedCandidateCheckpoint := by
  intro H D pub physical proof split hash obs bytes run
  obtain ⟨p,scratch,zero,a,hzero,hprepare,_,_,hcheckpoint⟩ :=
    XRk_Tx1Projection.cuts D pub physical proof split hash obs bytes run
  exact ⟨p,scratch,zero,a,hzero,hprepare,hcheckpoint⟩
#print axioms candidateTx1AcceptedPath
#print axioms acceptedCandidateCheckpoint
end XRk_Tx1Association

import PV_L1F_SourceRead
import PV_L1F_ReturnedPrefix
set_option autoImplicit false
noncomputable section
namespace PV_L1F_ActualPublication
open Aeneas Aeneas.Std ProverRwFull R1Z
open ProverRwRetryModel PV_RJ4IDB
variable [ExternalTypes] [ExternalFuns]
/-- Publication count is read from actual RetriedProof.attempts.val; earlier
count and rejection events remain as the independently acquired prior. -/
theorem source_publication_read
 (out : Result (core.result.Result prover.RetriedProof verifier.Error × Store))
 (prior : List Event) :
 (counts (prior++PV_L1F_ReturnedPrefix.suffix
   (ProverCommitSemanticTransport26.mapR sourceOutput out)),
  rejections (prior++PV_L1F_ReturnedPrefix.suffix
   (ProverCommitSemanticTransport26.mapR sourceOutput out))) =
 (counts prior++(PV_L1F_ReturnedCount.sourceRead out).toList,rejections prior) := by
 rw [PV_L1F_ReturnedPrefix.ordered_acquisition,PV_L1F_ReturnedCount.source_read]
#print axioms source_publication_read
end PV_L1F_ActualPublication

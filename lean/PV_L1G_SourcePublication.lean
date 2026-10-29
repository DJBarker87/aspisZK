import PV_L1G_CountPrefixes
import PV_L1F_ReturnedPrefix
set_option autoImplicit false
namespace PV_L1G_SourcePublication
open Aeneas Aeneas.Std
open PV_RJ4IDB R1Z.PV_W_Threading
/-- The prefix is acquired from an independent full source Run. The return
field is read from the extracted RetriedProof, not from a native projection.
A concrete native prefix encoder and its adequacy remain required. -/
theorem actual_count_with_prefix {W C E A : Type}
 [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]
 (encode : W × C → List Event) (prior : Run W C E A)
 (out : Result (core.result.Result ProverRwFull.prover.RetriedProof
  ProverRwFull.verifier.Error × R1Z.ProverRwRetryModel.Store)) :
 PV_L1G_CountPrefixes.channels
   (PV_L1G_WorldCapture.word encode prior ++ PV_L1F_ReturnedPrefix.suffix
     (R1Z.ProverCommitSemanticTransport26.mapR R1Z.ProverRwRetryModel.sourceOutput out)) =
 (counts (PV_L1G_WorldCapture.word encode prior) ++
    (PV_L1F_ReturnedCount.sourceRead out).toList,
  rejections (PV_L1G_WorldCapture.word encode prior)) := by
 exact (PV_L1F_ReturnedPrefix.ordered_acquisition _ _).trans (by
   rw [PV_L1F_ReturnedCount.source_read])
#print axioms actual_count_with_prefix
end PV_L1G_SourcePublication

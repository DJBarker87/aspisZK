import PV_L1F_ReturnedCount
set_option autoImplicit false
noncomputable section
namespace PV_L1F_SourceRead
open Aeneas Aeneas.Std ProverRwFull R1Z
open ProverRwRetryModel ProverCommitSemanticTransport26
variable [ExternalTypes] [ExternalFuns]
/-- Complete actual source readout, without a native event projection. The
same callback, original state, fuel and source retry are used on both sides. -/
theorem actual_retry_count {C : Type} (entropy : Entropy C) (pub : Pub)
 (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
 (store : Store) (callback : C) (k : Usize) (n : Nat) (bound : k.val+n=8) :
 PV_L1F_ReturnedCount.sourceRead
   (prover.retry_attempt entropy pub compiled variant hash store callback k) =
 PV_L1F_ReturnedCount.read
   (ProverCommitRetry34.run (attempt entropy pub compiled variant hash) n k.val (callback,store)) := by
 rw [← PV_L1F_ReturnedCount.source_read,ProverRwRetryModel.retry entropy pub compiled variant hash store callback k n bound]
 exact PV_L1F_ReturnedCount.read_map_state Prod.snd _
#print axioms actual_retry_count

/-- Reporting preserves the source readout on all normal and abnormal Results,
consuming the existing effectful retry/output law rather than deleting effects. -/
theorem reported_source_count {C : Type} (entropy : Entropy C) (pub : Pub)
 (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
 (store : Store) (callback : C) (k : Usize) (n : Nat) (bound : k.val+n=8)
 (capture : PV_DIAG2.Capture)
 (a : Nat → (C × Store) → PV_DIAG2.Observed (ProverCommitRetry34.Step Proof × (C × Store)))
 (resultLaw : ∀ i s, (a i s).result = attempt entropy pub compiled variant hash i s) :
 PV_L1F_ReturnedCount.read
   (PV_DIAG2.finish capture (PV_DIAG2.runEffects a n k.val (callback,store))).result =
 PV_L1F_ReturnedCount.sourceRead
   (prover.retry_attempt entropy pub compiled variant hash store callback k) := by
 have law := congrArg PV_L1F_ReturnedCount.read
   (PV_DIAG2.final_source_result entropy pub compiled variant hash store callback k n bound capture a resultLaw)
 rw [PV_L1F_ReturnedCount.source_read] at law
 simpa only [ProverRwRetryModel.drop,PV_L1F_ReturnedCount.read_map_state] using law
#print axioms reported_source_count
end PV_L1F_SourceRead

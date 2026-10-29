import PV_RJ4IDB_ResultOutput
import PV_DIAG2_ClientRetry
import PV_DIAG2_ApiSink
set_option autoImplicit false
namespace PV_RJ4IDB
open Aeneas Aeneas.Std R1Z ProverCommitRetry34
variable {S P : Type}
theorem output_stop_iff (r : Result (Step (Published P) × S))
 (e : ProverCommitRetry34.Error) :
 resultOutput r = .stop e ↔ ∃ s, r = .ok (.stop e,s) := by
 cases r with
 | fail f => simp [resultOutput]
 | div => simp [resultOutput]
 | ok pair => rcases pair with ⟨step,s⟩;cases step <;> simp [resultOutput]

theorem reject_free_output (r : Result (Step (Published P) × S))
 (h : PV_DIAG2.RejectFree r) : resultOutput r ≠ .stop .Rejected := by
 intro bad
 obtain ⟨s,hs⟩ := (output_stop_iff r .Rejected).mp bad
 exact h s hs

/-- Same native client entropy callback interpretation as diag2's existing
source law, with the exact returned-output adapter applied. No earlier
rejection/capture/write prefix is removed by this final-status exclusion. -/
theorem client_no_rejected_output [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]
 {C E : Type}
 (generate : C → Usize → Result (core.result.Result ProverRwRetryModel.Secret E × C))
 (pub : ProverRwRetryModel.Pub) (compiled : ProverRwRetryModel.Compiled)
 (variant : ProverRwFull.transport.Variant) (hash : ProverRwRetryModel.Hash)
 (n k : Nat) (state : C × ProverRwRetryModel.Store) :
 resultOutput (run (ProverRwRetryModel.attempt (PV_DIAG2.clientEntropy generate)
 pub compiled variant hash) n k state) ≠ .stop .Rejected :=
 reject_free_output _ (PV_DIAG2.client_run_reject_free generate pub compiled variant hash n k state)
#print axioms output_stop_iff
#print axioms reject_free_output
#print axioms client_no_rejected_output
end PV_RJ4IDB

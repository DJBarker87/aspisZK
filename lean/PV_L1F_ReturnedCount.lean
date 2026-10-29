import PV_DIAG2_Exit
set_option autoImplicit false
namespace PV_L1F_ReturnedCount
open Aeneas Aeneas.Std
open R1Z.ProverCommitRetry34
/-- Read the count from the returned record; no earlier event is reconstructed. -/
def read {P S : Type} : Result (Step (Published P) × S) → Option Nat
 | .ok (.done p,_) => some p.attempts
 | _ => none

theorem finish_read {P S : Type} (capture : PV_DIAG2.Capture)
 (x : PV_DIAG2.Observed (Step (Published P) × S)) :
 read (PV_DIAG2.finish capture x).result = read x.result := by
 rw [PV_DIAG2.finish_result]
#print axioms finish_read

theorem read_done {P S : Type} (p : Published P) (s : S) :
 read (.ok (.done p,s)) = some p.attempts := rfl
#print axioms read_done

theorem read_map_state {P S T : Type} (project : S → T)
 (out : Result (Step (Published P) × S)) :
 read (R1Z.ProverCommitSemanticTransport26.mapR (fun v => (v.1,project v.2)) out) =
 read out := by
 cases out with
 | fail e => rfl
 | div => rfl
 | ok pair => rcases pair with ⟨step,s⟩; cases step <;> rfl
#print axioms read_map_state

/-- Native extraction's actual RetriedProof field, on all outer outcomes. -/
noncomputable def sourceRead [ProverRwFull.ExternalTypes]
 (out : Result (core.result.Result ProverRwFull.prover.RetriedProof
    ProverRwFull.verifier.Error × R1Z.ProverRwRetryModel.Store)) : Option Nat :=
 match out with
 | .ok (.Ok p,_) => some p.attempts.val
 | _ => none

/-- Count is acquired directly from the actual returned record, including its
machine-word-to-Nat projection; sourceOutput is only the proved control adapter. -/
theorem source_read [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]
 (out : Result (core.result.Result ProverRwFull.prover.RetriedProof
    ProverRwFull.verifier.Error × R1Z.ProverRwRetryModel.Store)) :
 read (R1Z.ProverCommitSemanticTransport26.mapR R1Z.ProverRwRetryModel.sourceOutput out) =
 sourceRead out := by
 cases out with
 | fail e => rfl
 | div => rfl
 | ok pair => rcases pair with ⟨status,s⟩; cases status <;> rfl
#print axioms source_read
end PV_L1F_ReturnedCount

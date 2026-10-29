import PV_DIAG2_Retry
set_option autoImplicit false
namespace PV_DIAG2
open Aeneas Aeneas.Std Result
open R1Z ProverCommitRetry34

def exportError : ProverCommitRetry34.Error → PV_DIAG2.Error
 | .Parse => .Parse
 | .Semantic => .Semantic
 | .Transcript => .Transcript
 | .Relation => .Relation
 | .Merkle => .Merkle
 | .Query => .Query
 | .Checkpoint => .Checkpoint
 | .Allocation => .Allocation
 | .Rejected => .Rejected
 | .AttemptsExhausted => .AttemptsExhausted
 | .Entropy => .Entropy

structure Capture where
 enabled : Bool
 pcs : List Nat
 rendered : String

/-- The complete retry Result is retained alongside the reporting events.
`Capture` must come from native execution; no public-frame premise is hidden
inside this data-only structure. The stderr event is a requested write. -/
def finish {S P : Type} (c : Capture)
    (x : Observed (Step (Published P) × S)) : Observed (Step (Published P) × S) :=
 match x.result with
 | .ok (.stop e,_) =>
   ⟨x.effects ++ (reportError (exportError e) c.pcs c.rendered c.enabled).effects,x.result⟩
 | _ => x

/-- Success cannot enter plan::err/Termination's returned-error arm. Earlier
callee effects, stdout printing, and post-proof file errors are not excluded. -/
theorem success_no_error_report {S P : Type} (c : Capture)
    (x : Observed (Step (Published P) × S)) (p : Published P) (s : S)
    (h : x.result = ok (.done p,s)) : finish c x = x := by
 simp only [finish,h]

/-- With capture disabled the selected unit error fixes the complete requested
stderr string. Occurrence is deliberately not inferred from this statement. -/
theorem stopped_report {S P : Type} (x : Observed (Step (Published P) × S))
    (e : ProverCommitRetry34.Error) (s : S) (pcs : List Nat)
    (h : x.result = ok (.stop e,s)) :
 (finish ⟨false,pcs,""⟩ x).effects =
 x.effects ++ [.returned (exportError e),
   .stderr ("Error: " ++ spelling (exportError e) ++ "\n")] := by
 simp only [finish,h,report_disabled]

theorem stopped_frames_disabled {S P : Type} (x : Observed (Step (Published P) × S))
    (e : ProverCommitRetry34.Error) (s : S) (a b : List Nat)
    (h : x.result = ok (.stop e,s)) :
 finish ⟨false,a,""⟩ x = finish ⟨false,b,""⟩ x := by
 simp only [finish,h,report_disabled]

theorem exhaustion_requested_text :
 spelling (exportError .AttemptsExhausted) = "AttemptsExhausted" := rfl

/-- Reporting cannot silently turn an error, panic abstraction, divergence,
or success with its public attempt count into a different Result. -/
theorem finish_result {S P : Type} (c : Capture)
    (x : Observed (Step (Published P) × S)) : (finish c x).result = x.result := by
 rcases x with ⟨events,result⟩
 unfold finish
 cases result with
 | fail e => rfl
 | div => rfl
 | ok pair =>
   rcases pair with ⟨step,after⟩
   cases step <;> rfl

/-- The final diagnostic product still consumes the source-faithful retry
Result equation; effects are retained in the first component. -/
theorem final_source_result [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]
    {C : Type} (entropy : ProverRwRetryModel.Entropy C)
    (pub : ProverRwRetryModel.Pub) (compiled : ProverRwRetryModel.Compiled)
    (variant : ProverRwFull.transport.Variant) (hash : ProverRwRetryModel.Hash)
    (store : ProverRwRetryModel.Store) (callback : C) (k : Usize) (n : Nat)
    (bound : k.val+n=8) (c : Capture)
    (a : Nat → (C × ProverRwRetryModel.Store) →
      Observed (Step ProverRwRetryModel.Proof × (C × ProverRwRetryModel.Store)))
    (resultLaw : ∀ i s, (a i s).result =
      ProverRwRetryModel.attempt entropy pub compiled variant hash i s) :
 ProverCommitSemanticTransport26.mapR ProverRwRetryModel.drop
   (finish c (runEffects a n k.val (callback,store))).result =
 ProverCommitSemanticTransport26.mapR ProverRwRetryModel.sourceOutput
   (ProverRwFull.prover.retry_attempt entropy pub compiled variant hash store callback k) := by
 rw [finish_result]
 exact source_retry_result entropy pub compiled variant hash store callback k n bound a resultLaw

#print axioms success_no_error_report
#print axioms stopped_report
#print axioms stopped_frames_disabled
#print axioms exhaustion_requested_text
#print axioms finish_result
#print axioms final_source_result
end PV_DIAG2

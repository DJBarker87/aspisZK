import PV_DIAG3_Drop
import PV_DIAG3_Formatter
/-! Result::Termination and attempt_print_to_stderr with owned Error.
Native print/capture leaves retain their own buffer/lock/Result cleanup.
Error destruction follows reporting, including ignored I/O errors. -/
set_option autoImplicit false
namespace PV_DIAG3
variable {S E : Type}
def attemptStderr (capture : Op S Bool) (writeAndDrop : Op S Unit) : Op S Unit :=
 sequence capture (fun captured => if captured then pure () else writeAndDrop)
def reportOwned (result : Except E Unit) (report dropError : E → Op S Unit)
 (doublePanic : Panic → Panic → Op S Unit) : Op S Nat :=
 match result with
 | .ok () => pure 0
 | .error e => sequence (scope (report e) (dropError e) doublePanic) (fun _ => pure 1)
def ignoredWrite {I : Type} (write : Op S (Except I Unit))
 (dropResult : Except I Unit → Op S Unit) : Op S Unit := sequence write dropResult


theorem reporting_success (r d : E → Op S Unit) (dp : Panic → Panic → Op S Unit) :
 reportOwned (.ok ()) r d dp = pure 0 := rfl
#print axioms reporting_success

theorem captured_stderr_no_global (cap : Op S Bool) (w : Op S Unit)
 (s t : S) (es : List Event) (h : cap s = ⟨es,t,.value true⟩) :
 attemptStderr cap w s = ⟨es,t,.value ()⟩ := by
 simp [attemptStderr,sequence,h,bind,prepend,pure]
#print axioms captured_stderr_no_global

theorem uncaptured_stderr_keeps_write (cap : Op S Bool) (w : Op S Unit)
 (s t : S) (es : List Event) (h : cap s = ⟨es,t,.value false⟩) :
 attemptStderr cap w s = prepend es (w t) := by
 simp [attemptStderr,sequence,h,bind]
#print axioms uncaptured_stderr_keeps_write

theorem ignored_write_error_cleanup {I : Type} (write : Op S (Except I Unit))
 (drop : Except I Unit → Op S Unit) (s t : S) (es : List Event) (e : I)
 (h : write s = ⟨es,t,.value (.error e)⟩) :
 ignoredWrite write drop s = prepend es (drop (.error e) t) := by
 simp only [ignoredWrite,sequence,h,bind]
#print axioms ignored_write_error_cleanup

theorem report_error_normal (e : E) (r d : E → Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t u : S) (rs ds : List Event)
 (hr : r e s = ⟨rs,t,.value ()⟩) (hd : d e t = ⟨ds,u,.value ()⟩) :
 reportOwned (.error e) r d dp s = ⟨rs++ds,u,.value 1⟩ := by
 simp [reportOwned,sequence,normal_drop_order () s t u rs ds (r e) (d e) dp hr hd,
 bind,prepend,pure]
#print axioms report_error_normal

theorem report_abort_no_error_drop (e : E) (r d : E → Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t : S) (es : List Event) (c : Crash)
 (h : r e s = ⟨es,t,.abort c⟩) :
 reportOwned (.error e) r d dp s = ⟨es,t,.abort c⟩ := by
 simp [reportOwned,sequence,scope_abort_no_cleanup es s t c (r e) (d e) dp h,bind]
#print axioms report_abort_no_error_drop

theorem report_diverge_no_error_drop (e : E) (r d : E → Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t : S) (es : List Event)
 (h : r e s = ⟨es,t,.diverge⟩) :
 reportOwned (.error e) r d dp s = ⟨es,t,.diverge⟩ := by
 simp [reportOwned,sequence,scope_diverge_no_cleanup es s t (r e) (d e) dp h,bind]
#print axioms report_diverge_no_error_drop

theorem report_panic_keeps_cleanup (e : E) (r d : E → Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t : S) (es : List Event) (p : Panic)
 (h : r e s = ⟨es,t,.panic p⟩) :
 reportOwned (.error e) r d dp s =
 bind (prepend es (unwind p (d e) dp t)) (fun _ => pure 1) := by
 simp only [reportOwned,sequence,scope_panic es s t p (r e) (d e) dp h]
#print axioms report_panic_keeps_cleanup
end PV_DIAG3

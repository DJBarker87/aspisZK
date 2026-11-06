import NLC_FinishStep
import AuS1_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code Log run)
/-- Local analogue of NHZ_DRIVER: the finish model uses PreparedHashCode's
stateful digest syntax. No normalization, sorting or digest realization is assumed. -/
def fold {H : Type} : Nat → State H → Code (Out H)
 | 0, _ => liftM (fail .panic)
 | n+1, s => do
   let next ← step s
   match next with
   | .inl out => pure out
   | .inr after => fold n after
/-- A source invocation on ONE state. This is deliberately not a native cut
producer: each head equation needs a reviewed native cut and SAME child laws
before this conditional composition could participate in a row root. -/
inductive Invocation {H : Type} : Nat → State H → Result (Out H) → Log → List Event → Prop where
 | returned {n : Nat} {s : State H} {out : Out H} {log : Log}
   (head : run (step s) = (log,ok (.inl out))) : Invocation (n+1) s (ok out) log [s.next]
 | next {n : Nat} {s after : State H} {out : Result (Out H)} {log suffix : Log} {events : List Event}
   (head : run (step s) = (log,ok (.inr after)))
   (tail : Invocation n after out suffix events) :
   Invocation (n+1) s out (log ++ suffix) (s.next :: events)
 | fail {n : Nat} {s : State H} {error : Error} {log : Log}
   (head : run (step s) = (log,fail error)) : Invocation (n+1) s (fail error) log [s.next]
 | div {n : Nat} {s : State H} {log : Log}
   (head : run (step s) = (log,div)) : Invocation (n+1) s div log [s.next]
/-- Every Err is a returned value, while outer fail/div stop at their entered
occurrence. No caller-supplied success or endpoint is claimed as a row root. -/
theorem fold_from_steps {H : Type} {n : Nat} {s : State H}
 {out : Result (Out H)} {log : Log} {events : List Event}
 (cuts : Invocation n s out log events) : run (fold n s) = (log,out) := by
 induction cuts with
 | returned head =>
   simp only [fold]
   change run (PreparedHashCode.bind _ _) = _
   rw [AuS1_Trace.run_bind,head]
   simp only [AuS1_Trace.continueRun,run,List.append_nil]
 | next head _ ih =>
   simp only [fold]
   change run (PreparedHashCode.bind _ _) = _
   rw [AuS1_Trace.run_bind,head]
   simp only [AuS1_Trace.continueRun,ih]
 | fail head =>
   simp only [fold]
   change run (PreparedHashCode.bind _ _) = _
   rw [AuS1_Trace.run_bind,head]
   rfl
 | div head =>
   simp only [fold]
   change run (PreparedHashCode.bind _ _) = _
   rw [AuS1_Trace.run_bind,head]
   rfl
#print axioms fold_from_steps
#print fold_from_steps
end AspisR1.NLC_Finish
end

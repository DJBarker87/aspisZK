import PV_DIAG2_Retry
set_option autoImplicit false
namespace PV_DIAG2
open Aeneas Aeneas.Std Result
open R1Z ProverCommitRetry34

inductive Sink where
 | stdout | stderr | returned | capture | panic | oom | foreign
 deriving DecidableEq

def belongs : Sink → Effect → Bool
 | .stdout,.stdout _ => true
 | .stderr,.stderr _ => true
 | .returned,.returned _ => true
 | .capture,.capture _ => true
 | .panic,.panic _ _ => true
 | .oom,.oom _ _ => true
 | .foreign,.foreign _ _ => true
 | _,_ => false

def atSink (sink : Sink) (effects : List Effect) : List Effect := effects.filter (belongs sink)

/-- All actual per-attempt effects along the taken path. No callee trace is
replaced by []. Administrative entered/rejected records are separate. -/
def leafEffects {S P : Type} (a : Nat → S → Observed (Step P × S)) :
 Nat → Nat → S → List Effect
 | 0,_,_ => []
 | n+1,k,s =>
   let first := a k s
   first.effects ++ match first.result with
    | .ok (.retry,next) => leafEffects a n (k+1) next
    | _ => []

/-- Per-sink exact controller theorem. It proves absence of *direct*
controller diagnostics for every path, without asserting callee silence. -/
theorem retry_sink_exact {S P : Type} (a : Nat → S → Observed (Step P × S))
    (sink : Sink) (n k : Nat) (s : S) :
 atSink sink (runEffects a n k s).effects = atSink sink (leafEffects a n k s) := by
 induction n generalizing k s with
 | zero => rfl
 | succ n ih =>
   simp only [runEffects,leafEffects]
   cases h : (a k s).result with
   | fail e => simp [atSink,belongs]
   | div => simp [atSink,belongs]
   | ok pair =>
     rcases pair with ⟨step,next⟩
     cases step with
     | done p => simp [atSink,belongs]
     | stop e => simp [atSink,belongs]
     | retry =>
       simp only [atSink,List.filter_cons,belongs,List.filter_append,Bool.false_eq_true,if_false]
       exact congrArg (fun rest => List.filter (belongs sink) (a k s).effects ++ rest) (ih (k+1) next)

/-- This conditional composes an independently proved honest per-attempt
silence law. It does not provide that law or discard earlier rejected work. -/
theorem retry_sink_silent {S P : Type} (a : Nat → S → Observed (Step P × S))
    (sink : Sink) (silent : ∀ k s, atSink sink (a k s).effects = [])
    (n k : Nat) (s : S) : atSink sink (runEffects a n k s).effects = [] := by
 rw [retry_sink_exact]
 induction n generalizing k s with
 | zero => rfl
 | succ n ih =>
   simp only [leafEffects,atSink,List.filter_append]
   have hs := silent k s
   unfold atSink at hs
   rw [hs]
   cases h : (a k s).result with
   | fail e => rfl
   | div => rfl
   | ok pair =>
     rcases pair with ⟨step,next⟩
     cases step with
     | done p => rfl
     | stop e => rfl
     | retry => exact ih (k+1) next

/-- Result preservation remains orthogonal to all per-sink projections. -/
theorem sink_projection_retains_result {S P : Type}
    (a : Nat → S → Observed (Step P × S)) (n k : Nat) (s : S) :
 (runEffects a n k s).result = run (eraseAttempt a) n k s := erase_run a n k s

#print axioms retry_sink_exact
#print axioms retry_sink_silent
#print axioms sink_projection_retains_result
end PV_DIAG2

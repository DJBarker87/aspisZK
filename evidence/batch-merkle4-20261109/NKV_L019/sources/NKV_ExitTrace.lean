import NKV_BoundedLoop
set_option autoImplicit false
noncomputable section
namespace NKV_ExitTrace
open Aeneas Aeneas.Std Result ControlFlow
open NKV_StepErasure NKV_LoopTransport NKV_ReturnBoundary

/-- Source-ordered eventful cut execution. A step records the complete ordered
prefix emitted at that step, including the aborting/rejecting call. This is an
algebraic support relation; its concrete child events must still be installed. -/
inductive TraceWalk {S O E : Type} (body : S → List E × Result (ControlFlow S O)) :
 S → List E → Result O → Prop where
 | done (s : S) (events : List E) (out : O)
     (step : body s=(events,ok (.done out))) : TraceWalk body s events (ok out)
 | failed (s : S) (events : List E) (e : Error)
     (step : body s=(events,fail e)) : TraceWalk body s events (fail e)
 | diverged (s : S) (events : List E)
     (step : body s=(events,div)) : TraceWalk body s events div
 | next (s t : S) (first rest : List E) (out : Result O)
     (step : body s=(first,ok (.cont t)))
     (tail : TraceWalk body t rest out) : TraceWalk body s (first++rest) out

/-- Ghost Result erasure changes neither an emitted event nor its order.
Error/abort constructors have no continuation field and hence no later event. -/
theorem transport {S O P E : Type} (f : O → P)
 (body : S → List E × Result (ControlFlow S O))
 (target : S → List E × Result (ControlFlow S P))
 (same : ∀ s,target s=((body s).1,mapResult (mapFlow f) (body s).2))
 (s : S) (events : List E) (out : Result O) (walk : TraceWalk body s events out) :
 TraceWalk target s events (mapResult f out) := by
 induction walk with
 | done s events out step =>
   apply TraceWalk.done
   rw [same s,step];rfl
 | failed s events e step =>
   apply TraceWalk.failed
   rw [same s,step];rfl
 | diverged s events step =>
   apply TraceWalk.diverged
   rw [same s,step];rfl
 | next s t first rest out step tail ih =>
   apply TraceWalk.next s t first rest _ _ ih
   rw [same s,step];rfl

/-- Forgetting ghost events recovers the actual value-level loop, including
fail/div. No conclusion equates two independently supplied endpoint witnesses. -/
theorem value {S O E : Type} (body : S → List E × Result (ControlFlow S O))
 (s : S) (events : List E) (out : Result O) (walk : TraceWalk body s events out) :
 Walk (fun s => (body s).2) s out := by
 induction walk with
 | done s events out step => apply Walk.done;rw [step]
 | failed s events e step => apply Walk.failed;rw [step]
 | diverged s events step => apply Walk.diverged;rw [step]
 | next s t first rest out step tail ih => apply Walk.next s t out _ ih;rw [step]

/-- Applying terminal rejection to two identical full prefixes preserves that
prefix exactly and appends no event. This is conditional support, not the
missing concrete source/query dictionary installation. -/
theorem terminal {E : Type} (events : List E) (out : Out)
 (well : WellClassified out) :
 observeTrace events (cohort out)=observeTrace events (returned out) :=
 prefix_transport events out well

set_option pp.proofs false
#print transport
#print terminal
#print axioms transport
#print axioms value
#print axioms terminal
end NKV_ExitTrace
end

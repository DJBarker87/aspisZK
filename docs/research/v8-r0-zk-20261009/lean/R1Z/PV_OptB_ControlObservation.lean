import R1Z.PV_OptB_ControlRelation
set_option autoImplicit false
namespace R1Z.PV_OptB_ControlObservation
open Aeneas Aeneas.Std Result ProverCommitRetry34 PV_OptB_ControlRelation

/-- Only proof payloads are ignored here. The result retains interpreter
failure/divergence and an arbitrary full public OS observation of final state.
It is a signal theorem, not a replacement for the endpoint ROM observer. -/
def observation {S P E : Type} (read : S → E) : Result (Step P × S) → Result E
  | .fail e => .fail e
  | .div => .div
  | .ok (_,s) => .ok (read s)

theorem observation_equal {S T P Q E : Type} (R : S → T → Prop)
    (leftRead : S → E) (rightRead : T → E)
    (preserved : ∀ s t, R s t → leftRead s = rightRead t)
    (left : Result (Step P × S)) (right : Result (Step Q × T))
    (related : Related R left right) : observation leftRead left = observation rightRead right := by
  cases related with
  | failed e => rfl
  | diverged => rfl
  | done p q s t h => exact congrArg (fun e : E => (ok e : Result E)) (preserved s t h)
  | retry s t h => exact congrArg (fun e : E => (ok e : Result E)) (preserved s t h)
  | stop e s t h => exact congrArg (fun e : E => (ok e : Result E)) (preserved s t h)

#print axioms observation_equal
end R1Z.PV_OptB_ControlObservation

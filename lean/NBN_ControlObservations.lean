import NBN_StatementCut
set_option autoImplicit false
noncomputable section
namespace NBN_ControlObservations
open Aeneas Aeneas.Std Result
open NBN_StatementResult NBN_StatementCut

/-- Successful payment bytes are never inspected by the validator control cut. -/
theorem payment_bytes (s : Statement) (a b : Array U8 216#usize)
    (lane : core.result.Result U8 AE) (late : core.result.Result Unit LE) :
    run s (ok (.Ok a)) lane late = run s (ok (.Ok b)) lane late := by
  unfold run
  repeat' first | rfl | split

theorem payment_error_stops (s : Statement) (e : PE)
    (l1 l2 : core.result.Result U8 AE) (t1 t2 : core.result.Result Unit LE) :
    run s (ok (.Err e)) l1 t1 = run s (ok (.Err e)) l2 t2 := by
  unfold run
  repeat' first | rfl | split

theorem lane_error_stops (s : Statement)
    (pay : Result (core.result.Result (Array U8 216#usize) PE))
    (e : AE) (t1 t2 : core.result.Result Unit LE) :
    run s pay (.Err e) t1 = run s pay (.Err e) t2 := by
  unfold run tail
  rfl

#print axioms payment_bytes
#print axioms payment_error_stops
#print axioms lane_error_stops
end NBN_ControlObservations

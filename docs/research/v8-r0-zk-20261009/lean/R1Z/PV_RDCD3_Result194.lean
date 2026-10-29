import Aeneas

namespace R1Z.PV_RDCD3_Result194
set_option autoImplicit false
open Aeneas Aeneas.Std Result
abbrev RustResult := core.result.Result
abbrev CF (T E : Type) := core.ops.control_flow.ControlFlow (RustResult core.convert.Infallible E) T

/-- Exact deployed Result::branch match, preserving the error payload. -/
def branch {T E : Type} (r : RustResult T E) : Result (CF T E) :=
  match r with
  | .Ok v => ok (.Continue v)
  | .Err e => ok (.Break (.Err e))

/-- Exact residual match; the Ok payload is uninhabited. The concrete circle
instantiation converts its error type by the identity From implementation. -/
def residual {T E : Type} (r : RustResult core.convert.Infallible E) : Result (RustResult T E) :=
  match r with
  | .Err e => ok (.Err e)
  | .Ok impossible => nomatch impossible

/-- Full question-mark law including every continuation failure/divergence;
no callback totality or success premise appears. -/
theorem question_mark {T U E : Type} (r : RustResult T E)
    (next : T → Result (RustResult U E)) :
    (do let cf ← branch r
        match cf with
        | .Continue v => next v
        | .Break error => residual error) =
      (match r with | .Ok v => next v | .Err e => ok (.Err e)) := by
  cases r <;> rfl

def okOr {T E : Type} (o : Option T) (e : E) : RustResult T E :=
  match o with | some v => .Ok v | none => .Err e

theorem ok_or_some {T E : Type} (v : T) (e : E) : okOr (some v) e = .Ok v := rfl

theorem ok_or_none {T E : Type} (e : E) : okOr (none : Option T) e = .Err e := rfl

def unwrapOrElse {T E : Type} (r : RustResult T E) (fallback : E → Result T) : Result T :=
  match r with | .Ok v => ok v | .Err e => fallback e

theorem unwrap_ok {T E : Type} (v : T) (fallback : E → Result T) :
    unwrapOrElse (.Ok v) fallback = ok v := rfl

theorem unwrap_error {T E : Type} (e : E) (fallback : E → Result T) :
    unwrapOrElse (.Err e) fallback = fallback e := rfl

#print axioms question_mark
#print axioms ok_or_some
#print axioms ok_or_none
#print axioms unwrap_ok
#print axioms unwrap_error
end R1Z.PV_RDCD3_Result194

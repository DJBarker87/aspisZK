import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_CircleControl
set_option autoImplicit false

def okOr {I E : Type} (o : Option I) (e : E) : core.result.Result I E :=
  match o with | none => .Err e | some i => .Ok i

def nativeInner {I P E : Type} (inverse : Result (Option I)) (make : I → Result P)
    (singular : E) : Result (core.result.Result P E) := do
  let o ← inverse
  match okOr o singular with
  | .Err e => ok (.Err e)
  | .Ok i => do let point ← make i; ok (.Ok point)

def nativeOod {P E : Type} (inner : Result (core.result.Result P E))
    (reject : Result Bool) (subfield : E) : Result (core.result.Result P E) := do
  let r ← inner
  match r with
  | .Err e => ok (.Err e)
  | .Ok point => do
    let bad ← reject
    if bad then ok (.Err subfield) else ok (.Ok point)

def owned {I P E : Type} (inverse : Result (Option I)) (make : I → Result P)
    (reject : Result Bool) (singular subfield : E) : Result (core.result.Result P E) := do
  let o ← inverse
  match o with
  | none => ok (.Err singular)
  | some i => do
    let point ← make i
    let bad ← reject
    if bad then ok (.Err subfield) else ok (.Ok point)

/-- The ok_or/? control transport is independent of all field arithmetic and
preserves both Rust errors and outer failure/divergence, without totality hypotheses. -/
theorem native_owned {I P E : Type} (inverse : Result (Option I)) (make : I → Result P)
    (reject : Result Bool) (singular subfield : E) :
    nativeOod (nativeInner inverse make singular) reject subfield=
      owned inverse make reject singular subfield := by
  cases inverse with
  | fail e => rfl
  | div => rfl
  | ok o =>
    cases o with
    | none => rfl
    | some i =>
      simp only [nativeOod,nativeInner,owned,okOr,bind_tc_ok]
      cases make i <;> rfl

def unwrapOrElse {P E : Type} (r : core.result.Result P E) (fallback : E → Result P) :
    Result P := match r with | .Ok p => ok p | .Err e => fallback e

theorem unwrap_source {P E : Type} (r : core.result.Result P E) (fallback : E → Result P) :
    unwrapOrElse r fallback=(match r with | .Ok p => ok p | .Err e => fallback e) := rfl

#print axioms okOr
#print axioms nativeInner
#print axioms nativeOod
#print axioms owned
#print axioms native_owned
#print axioms unwrapOrElse
#print axioms unwrap_source
end R1Z.PV_AL_CircleControl

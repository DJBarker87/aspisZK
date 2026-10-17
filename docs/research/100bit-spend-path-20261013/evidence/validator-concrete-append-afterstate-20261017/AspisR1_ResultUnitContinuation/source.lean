import Aeneas.Std

/-! Generic checked-guard continuation, avoiding source-field evaluation. -/
set_option autoImplicit false
namespace AspisR1.ResultUnitContinuation
open Aeneas Aeneas.Std Result

def andThenUnit {E B : Type} (checks : Result (core.result.Result Unit E))
    (next : Result (core.result.Result B E)) : Result (core.result.Result B E) := do
  let check ← checks
  match check with
  | core.result.Result.Err e => ok (core.result.Result.Err e)
  | core.result.Result.Ok () => next

theorem andThenUnit_bind {A E B : Type} (m : Result A)
    (check : A → Result (core.result.Result Unit E)) (next : Result (core.result.Result B E)) :
    andThenUnit (do let x ← m; check x) next = (do let x ← m; andThenUnit (check x) next) := by
  cases m <;> rfl

theorem andThenUnit_if {E B : Type} (p : Prop) [Decidable p]
    (t f : Result (core.result.Result Unit E)) (next : Result (core.result.Result B E)) :
    andThenUnit (if p then t else f) next =
      if p then andThenUnit t next else andThenUnit f next := by
  by_cases hp : p
  · simp only [if_pos hp]
  · simp only [if_neg hp]

theorem andThenUnit_err {E B : Type} (e : E) (next : Result (core.result.Result B E)) :
    andThenUnit (.ok (core.result.Result.Err e)) next = .ok (core.result.Result.Err e) := rfl

theorem andThenUnit_ok {E B : Type} (next : Result (core.result.Result B E)) :
    andThenUnit (.ok (core.result.Result.Ok ())) next = next := rfl

theorem carry_then_unit {E C B : Type} (checks : Result (core.result.Result Unit E))
    (carry : Result C) (next : C → Result (core.result.Result B E)) :
    (do
      let result ← (do
        let check ← checks
        match check with
        | core.result.Result.Err e => ok (core.result.Result.Err e)
        | core.result.Result.Ok () => do let c ← carry; ok (core.result.Result.Ok c))
      match result with
      | core.result.Result.Err e => ok (core.result.Result.Err e)
      | core.result.Result.Ok c => next c) = andThenUnit checks (do let c ← carry; next c) := by
  cases checks with
  | fail err => rfl
  | div => rfl
  | ok check =>
    cases check with
    | Err err => rfl
    | Ok unit => cases unit; cases carry <;> rfl

#print axioms andThenUnit_bind
#print axioms andThenUnit_if
#print axioms andThenUnit_err
#print axioms andThenUnit_ok
#print axioms carry_then_unit
end AspisR1.ResultUnitContinuation

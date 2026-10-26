import R1Z.PV_RW_ResultOutcome
import R1Z.PV_RW_CursorLoop
set_option autoImplicit false
namespace R1Z.PV_RW_ResultListRun
open Aeneas Aeneas.Std Result

def run {T S : Type} (step : T → S → Result S) : List T → S → Result S
  | [], state => ok state
  | value::values, state => do
    let next ← step value state
    run step values next

theorem model {T S : Type} (step : T → S → Result S) (values : List T) (state : S) :
    PV_RW_ResultOutcome.toOutcome (run step values state)=
      PV_RW_CursorLoop.listRun (fun value state => PV_RW_ResultOutcome.toOutcome (step value state))
        values state := by
  induction values generalizing state with
  | nil => rfl
  | cons value values ih =>
    simp only [run,PV_RW_CursorLoop.listRun,PV_RW_ResultOutcome.bind]
    apply PV_RW_Outcome.congr
    intro next
    exact ih next

theorem congr {T S : Type} (left right : T → S → Result S)
    (same : ∀ value state, left value state=right value state) (values : List T) (state : S) :
    run left values state=run right values state := by
  apply PV_RW_ResultOutcome.injective
  rw [model,model]
  apply PV_RW_CursorLoop.congr
  intro value state
  exact congrArg PV_RW_ResultOutcome.toOutcome (same value state)
#print axioms model
#print axioms congr
end R1Z.PV_RW_ResultListRun

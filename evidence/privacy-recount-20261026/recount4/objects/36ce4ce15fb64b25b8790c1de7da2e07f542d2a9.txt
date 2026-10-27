import R1Z.PV_RW_Cursor
import R1Z.PV_RW_Outcome
set_option autoImplicit false
namespace R1Z.PV_RW_CursorLoop
open PV_RW_Cursor PV_RW_Outcome

def listRun {E T S : Type} (step : T → S → Outcome E S) : List T → S → Outcome E S
  | [], state => .ok state
  | value::values, state => bind (step value state) (listRun step values)

def bounded {E T S : Type} (step : T → S → Outcome E S) : Nat → Cursor T → S → Outcome E S
  | 0, _, _ => .div
  | fuel+1, cursor, state =>
    match PV_RW_Cursor.next cursor with
    | (none,_) => .ok state
    | (some value,next) => bind (step value state) (bounded step fuel next)

theorem complete {E T S : Type} (step : T → S → Outcome E S)
    (fuel : Nat) (cursor : Cursor T) (state : S)
    (bound : (remaining cursor).length < fuel) :
    bounded step fuel cursor state=listRun step (remaining cursor) state := by
  induction fuel generalizing cursor state with
  | zero => omega
  | succ fuel ih =>
    by_cases active : cursor.index<cursor.values.length
    · rw [bounded,PV_RW_Cursor.some_step cursor active]
      rw [PV_RW_Cursor.contents_step cursor active]
      rw [PV_RW_Cursor.some_step cursor active]
      simp only [listRun]
      apply PV_RW_Outcome.congr
      intro next
      apply ih
      simp only [remaining,List.length_drop] at bound ⊢
      omega
    · have stopped : cursor.values.length≤cursor.index := by omega
      rw [bounded,PV_RW_Cursor.none_step cursor stopped,PV_RW_Cursor.exhausted cursor stopped]
      rfl

theorem exact_fuel {E T S : Type} (step : T → S → Outcome E S) (cursor : Cursor T) (state : S) :
    bounded step ((remaining cursor).length+1) cursor state=listRun step (remaining cursor) state :=
  complete step _ cursor state (by omega)

theorem arity16 {E T S : Type} (step : T → S → Outcome E S) (values : List T)
    (shape : values.length=16) (state : S) :
    bounded step 17 (Cursor.mk values 0) state=listRun step values state := by
  exact complete step 17 (Cursor.mk values 0) state (by
    simp only [remaining,List.drop_zero,shape]
    omega)

theorem congr {E T S : Type} (left right : T → S → Outcome E S)
    (same : ∀ value state, left value state=right value state)
    (values : List T) (state : S) : listRun left values state=listRun right values state := by
  induction values generalizing state with
  | nil => rfl
  | cons value values ih =>
    simp only [listRun,same]
    apply PV_RW_Outcome.congr
    intro next
    exact ih next

theorem append {E T S : Type} (step : T → S → Outcome E S)
    (left right : List T) (state : S) :
    listRun step (left++right) state=bind (listRun step left state) (listRun step right) := by
  induction left generalizing state with
  | nil => rfl
  | cons value values ih =>
    simp only [List.cons_append,listRun,PV_RW_Outcome.assoc]
    apply PV_RW_Outcome.congr
    intro next
    exact ih next

theorem fail_head {E T S : Type} (step : T → S → Outcome E S) (cursor : Cursor T)
    (state : S) (error : E) (fuel : Nat) (active : cursor.index<cursor.values.length)
    (failed : step cursor.values[cursor.index] state=.fail error) :
    bounded step (fuel+1) cursor state=.fail error := by
  rw [bounded,PV_RW_Cursor.some_step cursor active]
  exact congrArg (fun result => bind result (bounded step fuel {cursor with index := cursor.index+1})) failed

theorem div_head {E T S : Type} (step : T → S → Outcome E S) (cursor : Cursor T)
    (state : S) (fuel : Nat) (active : cursor.index<cursor.values.length)
    (diverged : step cursor.values[cursor.index] state=.div) :
    bounded step (fuel+1) cursor state=.div := by
  rw [bounded,PV_RW_Cursor.some_step cursor active]
  exact congrArg (fun result => bind result (bounded step fuel {cursor with index := cursor.index+1})) diverged
#print axioms complete
#print axioms exact_fuel
#print axioms arity16
#print axioms congr
#print axioms append
#print axioms fail_head
#print axioms div_head
end R1Z.PV_RW_CursorLoop

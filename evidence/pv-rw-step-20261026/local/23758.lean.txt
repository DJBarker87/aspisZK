import R1Z.PV_RW_CursorLoop
set_option autoImplicit false
namespace R1Z.PV_RW_CursorTrace
open PV_RW_Outcome PV_RW_CursorLoop

def instrument {E T S : Type} (step : T → S → Outcome E S) (value : T)
    (state : S × List T) : Outcome E (S × List T) :=
  map id (fun next => (next,state.2++[value])) (step value state.1)

theorem trace {E T S : Type} (step : T → S → Outcome E S) (values : List T)
    (state : S) (before : List T) :
    listRun (instrument step) values (state,before)=
      map id (fun next => (next,before++values)) (listRun step values state) := by
  induction values generalizing state before with
  | nil => simp only [listRun,map,List.append_nil]
  | cons value tail ih =>
    simp only [listRun,instrument]
    cases h : step value state with
    | fail error => rfl
    | div => rfl
    | ok next =>
      change listRun (instrument step) tail (next,before++[value])=_
      rw [ih]
      simp only [map,PV_RW_Outcome.bind,List.append_assoc,List.singleton_append]

-- The success trace contains every processed element, in source order.
theorem success_trace {E T S : Type} (step : T → S → Outcome E S) (values : List T)
    (state final : S) (success : listRun step values state=.ok final) :
    listRun (instrument step) values (state,[])=.ok (final,values) := by
  rw [trace,success]
  rfl

-- Projecting the ghost instrumentation preserves failure tags and divergence.
theorem erase {E T S : Type} (step : T → S → Outcome E S) (values : List T)
    (state : S) (before : List T) :
    map id Prod.fst (listRun (instrument step) values (state,before))=
      listRun step values state := by
  rw [trace,map_comp]
  exact map_id _
#print axioms trace
#print axioms success_trace
#print axioms erase
end R1Z.PV_RW_CursorTrace

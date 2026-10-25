import Hiq_RuntimeHistory
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_RuntimeAlgebra
open Hist_Store Hiq_RuntimeAction

theorem append (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (left right : List Action) :
    Hiq_RuntimeHistory.run ops id store (left ++ right) =
      let a := Hiq_RuntimeHistory.run ops id store left
      let b := Hiq_RuntimeHistory.run ops id a.1 right
      (b.1,a.2 ++ b.2) := by
  induction left generalizing store with
  | nil => rfl
  | cons action rest ih =>
    simp only [List.cons_append,Hiq_RuntimeHistory.run,ih,List.cons_append]

theorem length (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (actions : List Action) : (Hiq_RuntimeHistory.run ops id store actions).2.length = actions.length := by
  induction actions generalizing store with
  | nil => rfl
  | cons action rest ih =>
    simp only [Hiq_RuntimeHistory.run,List.length_cons,ih]

theorem prefix_events (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (left right : List Action) :
    (Hiq_RuntimeHistory.run ops id store left).2 <+:
      (Hiq_RuntimeHistory.run ops id store (left ++ right)).2 := by
  rw [append]
  exact List.prefix_append _ _

#print axioms append
#print axioms length
#print axioms prefix_events
end AspisR1.Hiq_RuntimeAlgebra
end

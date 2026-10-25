import Hiq_RuntimeAction
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_RuntimeHistory
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry Hiq_RuntimeAction

def run (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program) (store : Store) :
    List Action → Store × List S2X.AccountEvent
  | [] => (store,[])
  | action :: rest =>
    let head := Hiq_RuntimeAction.apply ops id store action
    let tail := run ops id head.1 rest
    (tail.1,head.2 :: tail.2)

theorem classified (ops : AdapterRw.Ops) (keyLaw : ops.op36 = Hist_Authority.keyEq)
    (id : S2W_ExtractionBoundary.Program) (store : Store) (actions : List Action) :
    Trace ops id store (run ops id store actions).2 (run ops id store actions).1 := by
  induction actions generalizing store with
  | nil => exact Trace.nil store
  | cons action rest ih =>
    exact Trace.cons (Hiq_RuntimeAction.classified ops keyLaw id store action)
      (ih (Hiq_RuntimeAction.apply ops id store action).1)

theorem protection (ops : AdapterRw.Ops) (keyLaw : ops.op36 = Hist_Authority.keyEq)
    (id : S2W_ExtractionBoundary.Program) (store : Store) (actions : List Action) (key : Nat)
    (owner : (store key).owner = id) (marker : Initialized (store key).data) :
    (∀ event ∈ (run ops id store actions).2, S2X.Preserves key event) ∧
      (run ops id store actions).1 key = store key :=
  Hist_TraceProtection.trace_frame ops id store _ key _ (classified ops keyLaw id store actions) owner marker

#print axioms classified
#print axioms protection
end AspisR1.Hiq_RuntimeHistory
end

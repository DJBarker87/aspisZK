import Lean
set_option autoImplicit false
namespace FinishContextTacticDiagnostic
inductive Carrier (T : Type) where
  | ok : T → Carrier T
  | fail : Carrier T

def bind {T U : Type} (input : Carrier T) (f : T → Carrier U) : Carrier U :=
  match input with
  | .ok x => f x
  | .fail => .fail

theorem bind_ok {T U : Type} (x : T) (f : T → Carrier U) :
    bind (.ok x) f = f x := rfl

def view {T : Type} (input : Carrier T) : Carrier (T × T) :=
  bind input (fun x => .ok (x,x))

theorem preserve_constructor {T : Type} (a b : T) (input : Carrier T)
    (hrun : input = .ok b) (hv : view input = .ok (a,a)) :
    Carrier.ok (b,b) = Carrier.ok (a,a) := by
  simp only [view,hrun,bind_ok] at hv
  trace_state
  exact hv

#print axioms preserve_constructor
end FinishContextTacticDiagnostic

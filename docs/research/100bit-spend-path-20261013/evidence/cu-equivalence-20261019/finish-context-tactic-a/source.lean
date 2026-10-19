import Lean
set_option autoImplicit false
namespace FinishContextTacticDiagnostic
inductive Carrier (T : Type) where
  | ok : T → Carrier T
  | fail : Carrier T

theorem simplifier_projects_constructor {T : Type} (a b : T)
    (h : Carrier.ok a = Carrier.ok b) : a = b := by
  simp only at h
  trace_state
  exact h

#print axioms simplifier_projects_constructor
end FinishContextTacticDiagnostic

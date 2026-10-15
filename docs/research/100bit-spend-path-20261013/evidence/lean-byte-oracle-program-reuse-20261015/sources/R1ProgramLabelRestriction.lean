import AspisV8R19.OracleProgramOps

/-! Restrict a program to labels satisfying a predicate, when every address
reachable in every continuation satisfies that predicate. -/
set_option autoImplicit false
namespace AspisR1.ProgramLabelRestriction

open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps

variable {I A O : Type}

def AllLabels (C : I → Prop) : Program I A O → Prop
  | .done _ => True
  | .ask i next => C i ∧ ∀ a, AllLabels C (next a)

def restrict (C : I → Prop) : (p : Program I A O) → AllLabels C p →
    Program {i : I // C i} A O
  | .done o, _ => .done o
  | .ask i next, h => .ask ⟨i, h.1⟩ (fun a => restrict C (next a) (h.2 a))

theorem rename_restrict (C : I → Prop) (p : Program I A O)
    (h : AllLabels C p) :
    rename Subtype.val (restrict C p h) = p := by
  induction p with
  | done o => rfl
  | ask i next ih =>
      rcases h with ⟨hi, hnext⟩
      simp only [restrict, rename]
      congr 1
      funext a
      exact ih a (hnext a)

#print axioms rename_restrict

end AspisR1.ProgramLabelRestriction

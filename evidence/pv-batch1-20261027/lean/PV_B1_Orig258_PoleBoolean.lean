import Std
set_option autoImplicit false
namespace PV_B1_Orig258_PoleBoolean
/-- The four shipped bitwise updates form exactly one row predicate. -/
def row (clear active a b c d : Bool) : Bool :=
  (((clear && !(active && a)) && !(active && b)) && !(active && c)) && !(active && d)

theorem row_value (clear active a b c d : Bool) :
    row clear active a b c d = (clear && !(active && (a || b || c || d))) := by
  cases clear <;> cases active <;> cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem inactive (clear a b c d : Bool) : row clear false a b c d = clear := by
  cases clear <;> rfl

theorem absorbing (active a b c d : Bool) : row false active a b c d = false := by
  rfl

theorem clear_iff (clear active a b c d : Bool) :
    row clear active a b c d = true ↔
      clear = true ∧ (active = true → a = false ∧ b = false ∧ c = false ∧ d = false) := by
  cases clear <;> cases active <;> cases a <;> cases b <;> cases c <;> cases d <;> decide
#print axioms row_value
#print axioms inactive
#print axioms absorbing
#print axioms clear_iff
end PV_B1_Orig258_PoleBoolean

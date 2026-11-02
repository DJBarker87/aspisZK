import PV_B3P_PanicPatterns571227
namespace PV_B3P_ControlFlowAssertion571227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Rust ControlFlow's source variant order: Continue=0, Break=1. This
observation is separate from any payload, destructor or unwind behaviour. -/
def discriminant {α β : Type} : ControlFlow α β → Nat
  | .cont _ => 0
  | .done _ => 1

def break_payload {α β : Type} : ControlFlow α β → Option β
  | .cont _ => none
  | .done value => some value

theorem nested_break_payload {α β γ : Type} (value : γ) :
    break_payload (ControlFlow.done (α := α) (ControlFlow.done (α := β) value)) =
      some (ControlFlow.done (α := β) value) := rfl

/-- The captured initializer residual arm explicitly builds Break(Break(x))
before extracting the inner residual. Thus its later discriminant assertion is
true for every payload, rather than inferred from a successful overall run. -/
theorem constructed_break_test {α β : Type} (value : β) :
    (discriminant (ControlFlow.done (α := α) value) == 1) = true := rfl

theorem constructed_assertion {α β γ : Type} (value : β)
    (normal first second : Result γ) :
    ¬ diagnostic ((discriminant (ControlFlow.done (α := α) value) == 1) = true) ∧
      branch ((discriminant (ControlFlow.done (α := α) value) == 1) = true) normal first =
        branch ((discriminant (ControlFlow.done (α := α) value) == 1) = true) normal second :=
  (assertion _ true normal first second).2 (constructed_break_test value)

#print axioms nested_break_payload
#print axioms constructed_break_test
#print axioms constructed_assertion
end PV_B3P_ControlFlowAssertion571227

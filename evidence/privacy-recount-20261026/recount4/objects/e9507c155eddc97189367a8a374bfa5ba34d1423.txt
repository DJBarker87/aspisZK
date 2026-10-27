import Aeneas
set_option autoImplicit false
namespace R1Z.ProverRw19LoopBind
open Aeneas Aeneas.Std Result ControlFlow

-- The generic loop equation, isolated from the inverse-field installation.
-- This is one symbolic step, with no concrete arithmetic or loop unrolling.
theorem loop_bind {A B : Type} (step : A → Result (ControlFlow A B)) (a : A) :
    loop step a = (do
      let cf ← step a
      match cf with
      | .cont next => loop step next
      | .done out => .ok out) := by
  rw [loop]
  cases step a <;> rfl

#print axioms loop_bind
end R1Z.ProverRw19LoopBind

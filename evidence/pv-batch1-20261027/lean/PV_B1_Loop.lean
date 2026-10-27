import Aeneas
set_option autoImplicit false
noncomputable section
namespace PV_B1_Loop
open Aeneas Aeneas.Std Result ControlFlow

theorem bind {A B : Type} (step : A → Result (ControlFlow A B)) (a : A) :
    loop step a = (do
      let cf ← step a
      match cf with
      | .cont next => loop step next
      | .done out => .ok out) := by
  rw [loop]
  cases step a <;> rfl

#print axioms bind
end PV_B1_Loop

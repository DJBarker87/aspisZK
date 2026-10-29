import Aeneas
namespace R1Z.PV_RDCD3_LoopUnfold
open Aeneas Aeneas.Std Result ControlFlow
theorem loop_bind {A B : Type} (step : A → Result (ControlFlow A B)) (a : A) :
    loop step a = (do
      let cf ← step a
      match cf with
      | .cont next => loop step next
      | .done out => .ok out) := by
  rw [loop]
  cases step a <;> rfl


#print axioms loop_bind
end R1Z.PV_RDCD3_LoopUnfold

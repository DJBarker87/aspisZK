import PV_B1_Loop
set_option autoImplicit false
noncomputable section
namespace PV_B1_LoopSteps
open Aeneas Aeneas.Std Result ControlFlow

theorem done_step {A B : Type} (step : A → Result (ControlFlow A B))
    (a : A) (b : B) (h : step a = ok (done b)) : loop step a = ok b := by
  rw [PV_B1_Loop.bind,h]
  rfl

theorem continue_step {A B : Type} (step : A → Result (ControlFlow A B))
    (a next : A) (h : step a = ok (cont next)) : loop step a = loop step next := by
  rw [PV_B1_Loop.bind,h]
  rfl

theorem fail_step {A B : Type} (step : A → Result (ControlFlow A B))
    (a : A) (e : Error) (h : step a = fail e) : loop step a = fail e := by
  rw [PV_B1_Loop.bind,h]
  rfl
#print axioms done_step
#print axioms continue_step
#print axioms fail_step
end PV_B1_LoopSteps

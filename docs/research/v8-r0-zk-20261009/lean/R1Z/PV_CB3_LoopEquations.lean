import Aeneas
set_option autoImplicit false
namespace R1Z.PV_CB3_LoopEquations
open Aeneas Aeneas.Std Result ControlFlow

theorem done_step {α β : Type} (body : α → Result (ControlFlow α β))
    (x : α) (y : β) (h : body x = ok (done y)) : loop body x = ok y := by
  rw [loop,h]

theorem fail_step {α β : Type} (body : α → Result (ControlFlow α β))
    (x : α) (e : Error) (h : body x = fail e) : loop body x = fail e := by
  rw [loop,h]

theorem div_step {α β : Type} (body : α → Result (ControlFlow α β))
    (x : α) (h : body x = div) : loop body x = div := by
  rw [loop,h]

theorem continue_step {α β : Type} (body : α → Result (ControlFlow α β))
    (x y : α) (h : body x = ok (cont y)) : loop body x = loop body y := by
  rw [loop,h]

theorem congr_body {α β : Type} (left right : α → Result (ControlFlow α β))
    (h : ∀ x, left x = right x) (x : α) : loop left x = loop right x := by
  exact congrArg (fun body => loop body x) (funext h)
#print axioms done_step
#print axioms fail_step
#print axioms div_step
#print axioms continue_step
#print axioms congr_body
end R1Z.PV_CB3_LoopEquations

import R1Z.PV_CBL_ArrayKernel
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_ArrayUnfold
set_option autoImplicit false

theorem bind {A B : Type} (step : A → Result (ControlFlow A B)) (a : A) :
    loop step a = (do let cf ← step a
                     match cf with
                     | .cont next => loop step next
                     | .done out => .ok out) := by
  rw [loop]
  cases step a <;> rfl

theorem unfold_loop {T : Type} {N : Usize} (v : Slice T) (out : Array T N) (i : Usize) :
    PV_CBL_ArrayKernel.array_reference_loop v out i =
      (do let cf ← PV_CBL_ArrayKernel.array_reference_loop.body v out i
          match cf with
          | .done a => ok a
          | .cont (a,j) => PV_CBL_ArrayKernel.array_reference_loop v a j) := by
  unfold PV_CBL_ArrayKernel.array_reference_loop
  rw [bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro cf _
  cases cf with
  | done a => rfl
  | cont next => rcases next with ⟨a,j⟩; rfl
#print axioms bind
#print axioms unfold_loop
end R1Z.PV_CBL_ArrayUnfold

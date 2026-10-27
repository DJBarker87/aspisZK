import R1Z.PV_CBL_PopSlices
import R1Z.PV_CBL_ArrayUnfold
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_AL_PopUnfold
set_option autoImplicit false

theorem unfold_loop {T : Type} (v : Slice T) (out : alloc.vec.Vec T)
    (last i : Usize) :
    PV_CBL_PopSlices.pop_slices_reference_loop v out last i =
      (do let cf ← PV_CBL_PopSlices.pop_slices_reference_loop.body v last out i
          match cf with
          | .done a => ok a
          | .cont (a,j) => PV_CBL_PopSlices.pop_slices_reference_loop v a last j) := by
  unfold PV_CBL_PopSlices.pop_slices_reference_loop
  rw [PV_CBL_ArrayUnfold.bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro cf _
  cases cf with
  | done a => rfl
  | cont next => rcases next with ⟨a,j⟩; rfl
#print axioms unfold_loop
end R1Z.PV_AL_PopUnfold

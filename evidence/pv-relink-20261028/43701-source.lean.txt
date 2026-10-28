import R1Z.PV_AL_SplitFlat
import R1Z.PV_CBL_ArrayUnfold
import R1Z.PV_CBL_PopSlices
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_AL_RangeUnfold
set_option autoImplicit false

theorem same_body (v : Slice U8) (last : Usize) (out : alloc.vec.Vec U8) (i : Usize) :
    PV_AL_SplitFlat.copy_range_loop.body v last out i =
      PV_CBL_PopSlices.pop_slices_reference_loop.body v last out i := rfl

theorem same_loop (v : Slice U8) (last : Usize) (out : alloc.vec.Vec U8) (i : Usize) :
    PV_AL_SplitFlat.copy_range_loop v last out i =
      PV_CBL_PopSlices.pop_slices_reference_loop v out last i := rfl

theorem unfold_loop (v : Slice U8) (last : Usize) (out : alloc.vec.Vec U8) (i : Usize) :
    PV_AL_SplitFlat.copy_range_loop v last out i =
      (do let cf ← PV_AL_SplitFlat.copy_range_loop.body v last out i
          match cf with
          | .done a => ok a
          | .cont (a,j) => PV_AL_SplitFlat.copy_range_loop v last a j) := by
  unfold PV_AL_SplitFlat.copy_range_loop
  rw [PV_CBL_ArrayUnfold.bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro cf _
  cases cf with
  | done a => rfl
  | cont next => rcases next with ⟨a,j⟩; rfl

#print axioms same_body
#print axioms same_loop
#print axioms unfold_loop
end R1Z.PV_AL_RangeUnfold

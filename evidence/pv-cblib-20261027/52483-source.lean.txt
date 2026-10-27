import R1Z.PV_CBL_DigestSoft
import R1Z.PV_CBL_ArrayUnfold
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_DigestUpdateUnfold
set_option autoImplicit false
theorem unfold_loop (state : Array U32 8#usize) (blocks : U64)
    (buffer : Array U8 64#usize) (pos : Usize) (data : Slice U8) (i : Usize) :
    PV_CBL_DigestSoft.sha_update_soft_owned_loop state blocks buffer pos data i =
      (do let cf ← PV_CBL_DigestSoft.sha_update_soft_owned_loop.body data state blocks buffer pos i
          match cf with
          | .done a => ok a
          | .cont (s,c,b,p,j) => PV_CBL_DigestSoft.sha_update_soft_owned_loop s c b p data j) := by
  unfold PV_CBL_DigestSoft.sha_update_soft_owned_loop
  rw [PV_CBL_ArrayUnfold.bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro cf _
  cases cf with
  | done a => rfl
  | cont next => rcases next with ⟨s,c,b,p,j⟩; rfl
#print axioms unfold_loop
end R1Z.PV_CBL_DigestUpdateUnfold

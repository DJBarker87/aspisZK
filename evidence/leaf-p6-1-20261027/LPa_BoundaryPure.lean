import LPa_Boundary
import LPa_CanonicalAdd
import LPa_PureFold
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.Boundary

theorem loop_pure (p : Array aspis_core.field.QM31 28#usize) :
    loop p = (do
      let initial ← Array.index_usize p 0#usize
      ok (p.val.foldl LPa.Add.field initial)) := by
  unfold loop
  have same : aspis_core.field.QM31.add = (fun a b => ok (LPa.Add.field a b)) := by
    funext a b
    exact LPa.Add.model_field a b
  rw [same]
  simp only [LPa.walkM_pure]

#print axioms loop_pure
end LPa.Boundary

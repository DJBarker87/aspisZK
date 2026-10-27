import LPo_B_LPa_Boundary
import LPo_B_LPa_CanonicalAdd
import LPo_B_LPa_PureFold
open Aeneas Aeneas.Std Result
open LPl_Kit_Release
set_option autoImplicit false
namespace LPo.BA.Boundary

theorem loop_pure (p : Array aspis_core.field.QM31 28#usize) :
    loop p = (do
      let initial ← Array.index_usize p 0#usize
      ok (p.val.foldl LPo.BA.Add.field initial)) := by
  unfold loop
  have same : aspis_core.field.QM31.add = (fun a b => ok (LPo.BA.Add.field a b)) := by
    funext a b
    exact LPo.BA.Add.model_field a b
  rw [same]
  simp only [LPo.BA.walkM_pure]

#print axioms loop_pure
end LPo.BA.Boundary

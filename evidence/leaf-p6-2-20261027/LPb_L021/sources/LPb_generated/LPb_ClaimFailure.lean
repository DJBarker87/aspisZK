import LPb_PreparedSequence
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace LPb_ClaimFailure
/-- Once a scalar fails canonicality, later loop iterations do not execute
further scalar decoders or arithmetic in the supplied model. -/
theorem stopped_fold {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array XRk_Wide 29#usize) (point : Nat) (indices : List Nat) :
    indices.foldlM (LPb_ClaimStages.step sem y1 g point) none = ok none := by
  induction indices with
  | nil => rfl
  | cons l ls ih =>
    simpa only [List.foldlM_cons,LPb_ClaimStages.stopped_step,bind_tc_ok] using ih

theorem stopped_finish : LPb_ClaimStages.finish none = ok none := rfl
#print axioms stopped_fold
#print axioms stopped_finish
end LPb_ClaimFailure

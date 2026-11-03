import PV_EVHB_CallbackEffects
set_option autoImplicit false
namespace PV_EVHB_CallbackSelection
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime
variable [ExternalTypes]

/-- Only dictionary selection and the extracted constructor body are used.
Actual native destruction effects remain computations, never erased by selection. -/
theorem constructor_mapErr_view (ops : ExternalFuns)
    (selected : PV_EVH_OperatorFrames.Selection ops)
    {T E C F : Type} (inst : core.ops.function.FnOnce C E F)
    (da : E → Q Unit) (dc : C → Q Unit) (value : F) (closure : C)
    (result : core.result.Result T E)
    (body : ∀ e, inst.call_once closure e = .ok value)
    (ha : ∀ e, PartialView (da e) (.ok ()))
    (hc : PartialView (dc closure) (.ok ())) :
    PartialView (PV_EVHB_CallbackEffects.mapErr da dc value result closure)
      (ops.op12 inst result closure) := by
  rw [selected.mapErr]
  have source : PV_EVH_ResultOps.sourceMapErr inst result closure =
      .ok (match result with | .Ok x => .Ok x | .Err _ => .Err value) := by
    cases result with
    | Ok x => rfl
    | Err e => simp only [PV_EVH_ResultOps.sourceMapErr,body,bind_tc_ok]; rfl
  rw [source]
  exact PV_EVHB_CallbackEffects.mapErr_view da dc value closure result ha hc

#print axioms constructor_mapErr_view
end PV_EVHB_CallbackSelection

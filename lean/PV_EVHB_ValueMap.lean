import PV_EVHB_CallbackOutcomes
import PV_EVH_OperatorFrames
set_option autoImplicit false
namespace PV_EVHB_ValueMap
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime
variable [ExternalTypes]

def map {T E U : Type} (invoke : T → Q U) (unused : Q Unit)
    (r : core.result.Result T E) : Q (core.result.Result U E) :=
  match r with
  | .Ok x => do
    let value ← invoke x
    pure (.Ok value)
  | .Err e => do
    let _ ← unused
    pure (.Err e)

theorem source_view (ops : ExternalFuns) (selected : PV_EVH_OperatorFrames.Selection ops)
    {T E U F : Type} (inst : core.ops.function.FnOnce F T U) (closure : F)
    (invoke : T → Q U) (unused : Q Unit) (r : core.result.Result T E)
    (hi : ∀ x, PartialView (invoke x) (inst.call_once closure x))
    (hd : PartialView unused (.ok ())) :
    PartialView (map invoke unused r) (ops.op11 inst r closure) := by
  rw [selected.map]
  cases r with
  | Ok x => exact bind_view _ _ _ _ (hi x) (fun _ => lift_view _)
  | Err e =>
    exact bind_view _ _ (.ok ())
      (fun _ => .ok (core.result.Result.Err (T := U) e)) hd (fun _ => lift_view _)

/-- All outcomes and observations of the move/new callback survive unchanged
apart from the successful Result tag. No infallible native move is inferred. -/
theorem ok_run {T E U : Type} (invoke : T → Q U) (unused : Q Unit)
    (x : T) (w : State) :
    map (E := E) invoke unused (.Ok x) w =
      ⟨PV_EVHB_CallbackOutcomes.retag (core.result.Result.Ok (E := E)) (invoke x w).outcome,
        (invoke x w).state,(invoke x w).events⟩ :=
  PV_EVHB_CallbackOutcomes.bind_return_run _ _ _

theorem error_run {T E U : Type} (invoke : T → Q U) (unused : Q Unit)
    (e : E) (w : State) :
    map invoke unused (.Err e) w =
      ⟨PV_EVHB_CallbackOutcomes.retag (fun _ => core.result.Result.Err (T := U) e) (unused w).outcome,
        (unused w).state,(unused w).events⟩ :=
  PV_EVHB_CallbackOutcomes.bind_return_run _ _ _

#print axioms source_view
#print axioms ok_run
#print axioms error_run
end PV_EVHB_ValueMap

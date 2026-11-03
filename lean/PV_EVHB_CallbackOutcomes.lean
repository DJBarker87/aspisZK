import PV_EVHB_CallbackEffects
set_option autoImplicit false
namespace PV_EVHB_CallbackOutcomes
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime

def retag {A B : Type} (f : A → B) : Outcome A → Outcome B
  | .returned (.ok a) => .returned (.ok (f a))
  | .returned (.fail e) => .returned (.fail e)
  | .returned .div => .returned .div
  | .fault e => .fault e
  | .exhausted => .exhausted

/-- Returning a constructor changes only a successful value. Complete Result,
fault, divergence and exhaustion prefixes/states are otherwise identical. -/
theorem bind_return_run {A B : Type} (m : Q A) (f : A → B) (w : State) :
    PV_EVH_Runtime.bind m (fun a => PV_EVH_Runtime.lift (.ok (f a))) w =
      ⟨retag f (m w).outcome,(m w).state,(m w).events⟩ := by
  cases h : (m w).outcome with
  | fault e => simp only [PV_EVH_Runtime.bind,h,retag]
  | exhausted => simp only [PV_EVH_Runtime.bind,h,retag]
  | returned r => cases r <;>
      simp only [PV_EVH_Runtime.bind,h,PV_EVH_Runtime.lift,retag,List.append_nil]

theorem error_branch {T E C F : Type} (da : E → Q Unit) (dc : C → Q Unit)
    (value : F) (closure : C) (error : E) (w : State) :
    let r := PV_EVHB_CallbackEffects.construct da dc value closure error w
    PV_EVHB_CallbackEffects.mapErr (T := T) da dc value (.Err error) closure w =
      ⟨retag (core.result.Result.Err (T := T)) r.outcome,r.state,r.events⟩ :=
  bind_return_run _ _ _

theorem ok_branch {T E C F : Type} (da : E → Q Unit) (dc : C → Q Unit)
    (value : F) (closure : C) (x : T) (w : State) :
    let r := dc closure w
    PV_EVHB_CallbackEffects.mapErr (E := E) da dc value (.Ok x) closure w =
      ⟨retag (fun _ => core.result.Result.Ok (E := F) x) r.outcome,r.state,r.events⟩ :=
  bind_return_run _ _ _

#print axioms bind_return_run
#print axioms error_branch
#print axioms ok_branch
end PV_EVHB_CallbackOutcomes

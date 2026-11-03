import PV_EVH_RuntimeOperators
set_option autoImplicit false
namespace PV_EVHB_CallbackEffects
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime
variable [ExternalTypes]

/-- Constructor callback: argument destruction precedes capture destruction.
Each subcomputation retains its complete Result/fault/exhaustion and prefix. -/
def construct {E C F : Type} (dropArgument : E → Q Unit)
    (dropCapture : C → Q Unit) (value : F) (closure : C) (error : E) : Q F := do
  let _ ← dropArgument error
  let _ ← dropCapture closure
  pure value

/-- Typed installation at a reached constructor map_err site. The unused
capture is destroyed on Ok as well; no precomputed helper Result is supplied. -/
def mapErr {T E C F : Type} (dropArgument : E → Q Unit)
    (dropCapture : C → Q Unit) (value : F)
    (result : core.result.Result T E) (closure : C) : Q (core.result.Result T F) :=
  match result with
  | .Ok x => do
    let _ ← dropCapture closure
    pure (.Ok x)
  | .Err e => do
    let out ← construct dropArgument dropCapture value closure e
    pure (.Err out)

/-- Full outcome law, including source fail/div, runtime fault and exhausted.
This is stronger than a successful-result projection and preserves all state. -/
theorem construct_run {E C F : Type} (da : E → Q Unit) (dc : C → Q Unit)
    (value : F) (closure : C) (error : E) (w : State) :
    construct da dc value closure error w =
      match (da error w).outcome with
      | .fault f => ⟨.fault f,(da error w).state,(da error w).events⟩
      | .exhausted => ⟨.exhausted,(da error w).state,(da error w).events⟩
      | .returned (.fail e) => ⟨.returned (.fail e),(da error w).state,(da error w).events⟩
      | .returned .div => ⟨.returned .div,(da error w).state,(da error w).events⟩
      | .returned (.ok _) =>
        let r := dc closure (da error w).state
        ⟨(match r.outcome with
          | .fault f => .fault f
          | .exhausted => .exhausted
          | .returned (.fail e) => .returned (.fail e)
          | .returned .div => .returned .div
          | .returned (.ok _) => .returned (.ok value)),
          r.state,(da error w).events ++ r.events⟩ := by
  unfold construct
  cases h : (da error w).outcome with
  | fault f => simp only [Bind.bind,PV_EVH_Runtime.bind,h]
  | exhausted => simp only [Bind.bind,PV_EVH_Runtime.bind,h]
  | returned r =>
    cases r with
    | fail e => simp only [Bind.bind,PV_EVH_Runtime.bind,h]
    | div => simp only [Bind.bind,PV_EVH_Runtime.bind,h]
    | ok u =>
      cases hc : (dc closure (da error w).state).outcome with
      | fault f => simp only [Bind.bind,PV_EVH_Runtime.bind,h,hc,List.append_nil]
      | exhausted => simp only [Bind.bind,PV_EVH_Runtime.bind,h,hc,List.append_nil]
      | returned s => cases s <;>
          simp only [Bind.bind,PV_EVH_Runtime.bind,h,hc,Pure.pure,PV_EVH_Runtime.lift,List.append_nil]

theorem construct_view {E C F : Type} (da : E → Q Unit) (dc : C → Q Unit)
    (value : F) (closure : C) (error : E)
    (ha : PartialView (da error) (.ok ()))
    (hc : PartialView (dc closure) (.ok ())) :
    PartialView (construct da dc value closure error) (.ok value) :=
  bind_view _ _ (.ok ()) (fun _ => .ok value) ha
    (fun _ => bind_view _ _ (.ok ()) (fun _ => .ok value) hc (fun _ => lift_view _))

theorem mapErr_view {T E C F : Type} (da : E → Q Unit) (dc : C → Q Unit)
    (value : F) (closure : C) (result : core.result.Result T E)
    (ha : ∀ e, PartialView (da e) (.ok ()))
    (hc : PartialView (dc closure) (.ok ())) :
    PartialView (mapErr da dc value result closure)
      (.ok (match result with | .Ok x => .Ok x | .Err _ => .Err value)) := by
  cases result with
  | Ok x =>
    exact bind_view _ _ (.ok ()) (fun _ => .ok (core.result.Result.Ok (E := F) x)) hc (fun _ => lift_view _)
  | Err e =>
    exact bind_view _ _ (.ok value) (fun out => .ok (core.result.Result.Err (T := T) out))
      (construct_view da dc value closure e (ha e) hc) (fun _ => lift_view _)

#print axioms construct_run
#print axioms construct_view
#print axioms mapErr_view
end PV_EVHB_CallbackEffects

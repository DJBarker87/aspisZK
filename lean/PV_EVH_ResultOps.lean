import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_ResultOps
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes]
/-- Source-level standard operator bodies. Binding these selections to the
actual deployed dictionary is OPEN; selecting them is not native adequacy. -/
def sourceMap {T E U F : Type} (inst : core.ops.function.FnOnce F T U)
    (r : core.result.Result T E) (f : F) : Result (core.result.Result U E) :=
  match r with
  | .Ok value => do
    let out ← inst.call_once f value
    pure (.Ok out)
  | .Err e => pure (.Err e)

def sourceMapErr {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
    (r : core.result.Result T E) (f : O) : Result (core.result.Result T F) :=
  match r with
  | .Ok value => pure (.Ok value)
  | .Err e => do
    let out ← inst.call_once f e
    pure (.Err out)

@[reducible] def install (ops : ExternalFuns) : ExternalFuns :=
  {ops with op11 := sourceMap, op12 := sourceMapErr}

/-- The unused closure is explicitly dropped. A callback invocation owns
its consumed closure and argument's native effects, including capture/argument
drops and unwinding. -/
def map {T E U : Type} (callback : T → P U) (dropClosure : P Unit)
    (r : core.result.Result T E) : P (core.result.Result U E) :=
  match r with
  | .Ok value => do
    let out ← callback value
    pure (.Ok out)
  | .Err e => do
    let _ ← dropClosure
    pure (.Err e)

def mapErr {T E F : Type} (callback : E → P F) (dropClosure : P Unit)
    (r : core.result.Result T E) : P (core.result.Result T F) :=
  match r with
  | .Ok value => do
    let _ ← dropClosure
    pure (.Ok value)
  | .Err e => do
    let out ← callback e
    pure (.Err out)

theorem map_fixed {T E U F : Type} (ops : ExternalFuns)
    (inst : core.ops.function.FnOnce F T U) (f : F)
    (callback : T → P U) (dropClosure : P Unit)
    (hc : ∀ value, FinishedView (callback value) (inst.call_once f value))
    (hd : FinishedView dropClosure (.ok ())) (r : core.result.Result T E) :
    letI : ExternalFuns := install ops
    FinishedView (map callback dropClosure r) (core.result.Result.map inst r f) := by
  letI : ExternalFuns := install ops
  cases r with
  | Ok value =>
    change FinishedView (PV_EVH_Prefix.bind (callback value) (fun out => PV_EVH_Prefix.lift (.ok (core.result.Result.Ok (E := E) out))))
      (Aeneas.Std.bind (inst.call_once f value) (fun out => .ok (core.result.Result.Ok (E := E) out)))
    exact PV_EVH_Prefix.bind_fixed _ _ _ _ (hc value) (fun out => PV_EVH_Prefix.lift_fixed _)
  | Err e =>
    change FinishedView (PV_EVH_Prefix.bind dropClosure (fun _ => PV_EVH_Prefix.lift (.ok (core.result.Result.Err (T := U) e)))) (.ok (core.result.Result.Err (T := U) e))
    exact PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok (core.result.Result.Err (T := U) e)) hd
      (fun _ => PV_EVH_Prefix.lift_fixed _)

theorem mapErr_fixed {T E F O : Type} (ops : ExternalFuns)
    (inst : core.ops.function.FnOnce O E F) (f : O)
    (callback : E → P F) (dropClosure : P Unit)
    (hc : ∀ error, FinishedView (callback error) (inst.call_once f error))
    (hd : FinishedView dropClosure (.ok ())) (r : core.result.Result T E) :
    letI : ExternalFuns := install ops
    FinishedView (mapErr callback dropClosure r) (core.result.Result.map_err inst r f) := by
  letI : ExternalFuns := install ops
  cases r with
  | Ok value =>
    change FinishedView (PV_EVH_Prefix.bind dropClosure (fun _ => PV_EVH_Prefix.lift (.ok (core.result.Result.Ok (E := F) value)))) (.ok (core.result.Result.Ok (E := F) value))
    exact PV_EVH_Prefix.bind_fixed _ _ (.ok ()) (fun _ => .ok (core.result.Result.Ok (E := F) value)) hd
      (fun _ => PV_EVH_Prefix.lift_fixed _)
  | Err e =>
    change FinishedView (PV_EVH_Prefix.bind (callback e) (fun out => PV_EVH_Prefix.lift (.ok (core.result.Result.Err (T := T) out))))
      (Aeneas.Std.bind (inst.call_once f e) (fun out => .ok (core.result.Result.Err (T := T) out)))
    exact PV_EVH_Prefix.bind_fixed _ _ _ _ (hc e) (fun out => PV_EVH_Prefix.lift_fixed _)
#print axioms map_fixed
#print axioms mapErr_fixed
end PV_EVH_ResultOps

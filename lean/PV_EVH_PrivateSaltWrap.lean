import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_PrivateSaltWrap
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
abbrev Values := alloc.vec.Vec (Array U8 32#usize)

/-- Source model of the standard map control flow. Native callback/drop
adequacy and its binding to actual opsNative remain separate obligations. -/
def sourceMap {T E U F : Type} (inst : core.ops.function.FnOnce F T U)
    (r : core.result.Result T E) (f : F) : Result (core.result.Result U E) := do
  match r with
  | .Ok value =>
    let out ← inst.call_once f value
    pure (.Ok out)
  | .Err e => pure (.Err e)

@[reducible] def install (ops : ExternalFuns) : ExternalFuns := {ops with op11 := sourceMap}

def wrap (values : Values) : P host_commitment.PrivateSalts := pure values

theorem wrap_fixed (values : Values) :
    FinishedView (wrap values) (host_commitment.PrivateSalts.new values) :=
  PV_EVH_Prefix.lift_fixed (.ok values)

def map (r : core.result.Result Values verifier.Error) :
    P (core.result.Result host_commitment.PrivateSalts verifier.Error) :=
  match r with
  | .Ok values => do
    let wrapped ← wrap values
    pure (.Ok wrapped)
  | .Err e => pure (.Err e)

theorem map_fixed (ops : ExternalFuns) (r : core.result.Result Values verifier.Error) :
    letI : ExternalFuns := install ops
    FinishedView (map r)
      (core.result.Result.map (BuiltinFnOnce Values host_commitment.PrivateSalts) r
        host_commitment.PrivateSalts.new) := by
  letI : ExternalFuns := install ops
  cases r with
  | Ok values => exact PV_EVH_Prefix.lift_fixed (.ok (core.result.Result.Ok (E := verifier.Error) values))
  | Err e => exact PV_EVH_Prefix.lift_fixed (.ok (core.result.Result.Err (T := host_commitment.PrivateSalts) e))

/-- This identifies the inherited source-map lift with the independently
interpreted constructor callback, including its state and event trace. -/
theorem map_agrees (ops : ExternalFuns) (r : core.result.Result Values verifier.Error) :
    letI : ExternalFuns := install ops
    map r = PV_EVH_Prefix.lift
      (core.result.Result.map (BuiltinFnOnce Values host_commitment.PrivateSalts) r
        host_commitment.PrivateSalts.new) := by
  letI : ExternalFuns := install ops
  funext w
  cases r <;> rfl

theorem map_execution (r : core.result.Result Values verifier.Error) (w : World) :
    map r w = ⟨.finished (.ok (match r with | .Ok values => .Ok values | .Err e => .Err e)),w,[]⟩ := by
  cases r <;> rfl
#print axioms wrap_fixed
#print axioms map_fixed
#print axioms map_agrees
#print axioms map_execution
end PV_EVH_PrivateSaltWrap

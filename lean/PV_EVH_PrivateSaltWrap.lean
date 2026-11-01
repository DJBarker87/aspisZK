import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_PrivateSaltWrap
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
abbrev Values := alloc.vec.Vec (Array U8 32#usize)

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

theorem map_fixed (r : core.result.Result Values verifier.Error) :
    FinishedView (map r)
      (core.result.Result.map (BuiltinFnOnce Values host_commitment.PrivateSalts) r
        host_commitment.PrivateSalts.new) := by
  cases r with
  | Ok values => exact PV_EVH_Prefix.lift_fixed (.ok (.Ok values))
  | Err e => exact PV_EVH_Prefix.lift_fixed (.ok (.Err e))

theorem map_execution (r : core.result.Result Values verifier.Error) (w : World) :
    map r w = ⟨.finished (.ok (match r with | .Ok values => .Ok values | .Err e => .Err e)),w,[]⟩ := by
  cases r <;> rfl
#print axioms wrap_fixed
#print axioms map_fixed
#print axioms map_execution
end PV_EVH_PrivateSaltWrap

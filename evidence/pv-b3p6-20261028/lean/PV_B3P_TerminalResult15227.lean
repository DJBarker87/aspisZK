import PV_B3P_PartsBinding13227
namespace PV_B3P_Terminal15227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227 PV_B3P_Binding13227
set_option autoImplicit false
noncomputable section

def result_map15 {α β E : Type} (f : α → β) : core.result.Result α E → core.result.Result β E
  | .Ok value => .Ok (f value)
  | .Err error => .Err error

def result_map_error15 {α E F : Type} (f : E → F) : core.result.Result α E → core.result.Result α F
  | .Ok value => .Ok value
  | .Err error => .Err (f error)

theorem terminal_result_maps15 (result : core.result.Result Parts PE) :
    result_map_error15 (fun _ : PE => PV_B3P_227.aspis_core.state_only_prefix.r0.Error.Public) (result_map15 (fun parts : Parts => parts.1) result) =
      (match result with | .Ok parts => .Ok parts.1 | .Err _ => .Err PV_B3P_227.aspis_core.state_only_prefix.r0.Error.Public) := by
  cases result <;> rfl
#print axioms terminal_result_maps15
end
end PV_B3P_Terminal15227

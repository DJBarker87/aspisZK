import PV_B3P_TerminalResult15227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Terminal15227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227 PV_B3P_Binding13227
set_option autoImplicit false
noncomputable section

/-- Exact wrapper order: from_fn selection, semantic receiver conversion,
terminal_parts, map of tuple field zero, and map_err to Public. The source
library implementations of from_fn/map/map_err remain separately catalogued. -/
def terminal_source15 (base : ExternalTypes) (native : SourcePorts base)
    (p : Public base) (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (c : aspis_core.state_only_prefix.r0.Challenges) : Result (core.result.Result SQ SE) := do
  let selected ← native.select (PV_B3P_Carrier227.mapArray (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ) claims)
  let public1 ← native.semantic p
  let cs := PV_B3P_Carrier227.challenges c
  let result ← native.parts public1 selected (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ point)
    cs.lambda cs.chi cs.theta cs.zc cs.mu
  let projected := result_map15 (fun parts : Parts => parts.1) result
  .ok (result_map_error15 (fun _ : PE => PV_B3P_227.aspis_core.state_only_prefix.r0.Error.Public) projected)

theorem terminal_source_binding15 (base : ExternalTypes) (native : SourcePorts base)
    (p : Public base) (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize) (c : aspis_core.state_only_prefix.r0.Challenges) :
    terminal_source15 base native p claims point c = source_continuation base native p claims point c := by
  unfold terminal_source15 source_continuation
  apply PV_B3P_Binding9227.bind_equal9
  intro selected
  apply PV_B3P_Binding9227.bind_equal9
  intro public1
  apply PV_B3P_Binding9227.bind_equal9
  intro result
  cases result <;> rfl
#print axioms terminal_source_binding15
end
end PV_B3P_Terminal15227

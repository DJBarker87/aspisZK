from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean');files={}
h='''namespace PV_B3P_Terminal15227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227 PV_B3P_Binding13227
set_option autoImplicit false
noncomputable section
'''
files['PV_B3P_TerminalResult15227']='import PV_B3P_PartsBinding13227\n'+h+'''
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
'''
files['PV_B3P_TerminalSource15227']='import PV_B3P_TerminalResult15227\nimport PV_B3P_DigestCpsEq9227\n'+h+'''
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
'''
files['PV_B3P_TerminalInstall15227']='import PV_B3P_TerminalSource15227\nimport PV_B3P_SelectedCorrected14227\n'+h+'''
def terminal_native15 (base : ExternalTypes) (native : SourcePorts base)
    (p : Public base) (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize) (c : aspis_core.state_only_prefix.r0.Challenges) :=
  PV_B3P_Install227.transport (terminal_source15 base native p claims point c)

@[reducible] def source_install15 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) (native : SourcePorts base) :
    @ExternalFuns (PV_B3P_Install227.Types base) :=
  letI : ExternalTypes := PV_B3P_Install227.Types base
  { original with op227 := terminal_native15 base native }

theorem source_install_wrapper15 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) (native : SourcePorts base) :
    PV_B3P_Link_terminal_qm31 base (source_install15 base original native) native := by
  intro p claims point c
  exact congrArg PV_B3P_Install227.transport (terminal_source_binding15 base native p claims point c)

/-- One concrete model instance jointly satisfies the wrapper and all corrected
function links. This witness is never labelled deployed native closure. -/
theorem native_model_joint_witness15 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) :
    let native := source_ports13 base PV_B3P_227.reference_terminal.composition_parts
      PV_B3P_227.reference_terminal.equality_value
    PV_B3P_Link_terminal_qm31 base (source_install15 base original native) native ∧
      PV_B3P_Correct14227.CorrectedLinks14 PV_B3P_Correct14227.corrected_model_bodies14
        PV_B3P_Correct14227.frozen_calls14 PV_B3P_Correct14227.constructor14 57#usize := by
  exact ⟨source_install_wrapper15 base original _,PV_B3P_Correct14227.corrected_links_witness14⟩
#print axioms source_install_wrapper15
#print axioms native_model_joint_witness15
end
end PV_B3P_Terminal15227
'''
for m,s in files.items():(L/(m+'.lean')).write_text(s)
print(' '.join(files))

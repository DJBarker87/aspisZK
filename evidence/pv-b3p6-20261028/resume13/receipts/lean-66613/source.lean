import PV_B3P_SemanticBinding13227
import PV_B3P_SelectionBinding13227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_TopDown13227 Result ControlFlow Error
set_option autoImplicit false
abbrev CompositionFn13 := SP → Array SQ 84#usize → Array SQ 10#usize → SQ → SQ → SQ →
  Result (core.result.Result (SQ × Array SQ 16#usize × Array SQ 10#usize × SQ × SQ × SQ) PE)
def parts_with13
  (composition : CompositionFn13)
  (equality : Array SQ 10#usize → Array SQ 10#usize → Result SQ)
  (public1 : reference_terminal.SemanticPublic)
  (claims : Array aspis_core.field.QM31 84#usize)
  (point : Array aspis_core.field.QM31 10#usize)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31)
  (theta : aspis_core.field.QM31)
  (zerocheck_point : Array aspis_core.field.QM31 10#usize)
  (mu : aspis_core.field.QM31) :
  Result (core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 16#usize) × (Array aspis_core.field.QM31 10#usize)
    × aspis_core.field.QM31)
    reference_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  := do
  let r ←
    composition public1 claims point lambda chi theta
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (composition, c1, mask_only, g, h1_z, copy_active) := val
    let q ← equality zerocheck_point point
    let q1 ← aspis_core.field.QM31.mul q composition
    let q2 ← aspis_core.field.QM31.mul mu h1_z
    let q3 ← aspis_core.field.QM31.add q1 q2
    let q4 ← aspis_core.field.QM31.mul mu mu
    let q5 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE copy_active
    let q6 ← aspis_core.field.QM31.mul q5 h1_z
    let q7 ← aspis_core.field.QM31.mul q4 q6
    let original ← aspis_core.field.QM31.add q3 q7
    ok (core.result.Result.Ok (original, c1, mask_only, g))
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (aspis_core.field.QM31 × (Array aspis_core.field.QM31 16#usize) ×
      (Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
      (core.convert.FromSame
      reference_terminal.PoolV1PairForestSemanticTerminalErrorV1) residual

theorem parts_link13 (composition : CompositionFn13)
    (equality : Array SQ 10#usize → Array SQ 10#usize → Result SQ)
    (hc : PV_B3P_Links13227.PV_B3P_Link_terminal_composition_parts composition)
    (he : PV_B3P_Links13227.PV_B3P_Link_terminal_equality_value equality) :
    parts_with13 composition equality = reference_terminal.terminal_parts := by
  rw [hc,he]
  rfl

def source_ports13 (base : ProverRwFull.ExternalTypes) (composition : CompositionFn13)
    (equality : Array SQ 10#usize → Array SQ 10#usize → Result SQ) : SourcePorts base :=
  ⟨semantic_source13 base,source_selection13,parts_with13 composition equality⟩

section
variable (base : ProverRwFull.ExternalTypes)
local notation "terminal" => transported_reference base
/-- The callback conclusion with the source wrapper and its two changed callees
explicit. Other function/dependency links are prerequisites for discharging hc
and he; they have not been silently discharged by this conditional theorem. -/
theorem selected_callback13
    (ops : @ProverRwFull.ExternalFuns (PV_B3P_Install227.Types base))
    (composition : CompositionFn13)
    (equality : Array SQ 10#usize → Array SQ 10#usize → Result SQ)
    (wrapper : PV_B3P_Link_terminal_qm31 base ops (source_ports13 base composition equality))
    (hc : PV_B3P_Links13227.PV_B3P_Link_terminal_composition_parts composition)
    (he : PV_B3P_Links13227.PV_B3P_Link_terminal_equality_value equality)
    (self : @ProverRwFull.host_semantic.SemanticOracle (PV_B3P_Install227.Types base))
    (point : Array ProverRwFull.aspis_core.field.QM31 10#usize) :
    letI : ProverRwFull.ExternalTypes := PV_B3P_Install227.Types base
    ∀ claims,
      ops.op227 self.«public» claims point self.challenges =
        terminal self.«public» claims point self.challenges := by
  letI : ProverRwFull.ExternalTypes := PV_B3P_Install227.Types base
  exact PV_B3P_TopDown13227.selected_callback base ops (source_ports13 base composition equality)
    wrapper (semantic_source_binding13 base) source_selection_binding13 (parts_link13 composition equality hc he) self point
end
#print axioms parts_link13
#print axioms selected_callback13
end PV_B3P_Binding13227

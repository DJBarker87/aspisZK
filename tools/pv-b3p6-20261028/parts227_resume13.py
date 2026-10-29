"""Exact existing terminal_parts body with two explicit source callee slots.
No generated output is modified; this is an additional conditional source model.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';p=L/'PV_B3P_P227_14.lean';s=p.read_text();a=s.index('def reference_terminal.terminal_parts\n');b=s.index('\n/-- [',a);decl=s[a:b]
renamed=decl.replace('def reference_terminal.terminal_parts','def parts_with13\n  (composition : CompositionFn13)\n  (equality : Array SQ 10#usize → Array SQ 10#usize → Result SQ)',1).replace('reference_terminal.composition_parts public1','composition public1').replace('reference_terminal.equality_value zerocheck_point','equality zerocheck_point')
header='''import PV_B3P_SemanticBinding13227
import PV_B3P_SelectionBinding13227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_TopDown13227 Result ControlFlow Error
set_option autoImplicit false
abbrev CompositionFn13 := SP → Array SQ 84#usize → Array SQ 10#usize → SQ → SQ → SQ →
  Result (core.result.Result (SQ × Array SQ 16#usize × Array SQ 10#usize × SQ × SQ × SQ) PE)
'''
footer='''
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
'''
(L/'PV_B3P_PartsBinding13227.lean').write_text(header+renamed+footer)
(D/'resume13/parts-source-shape.json').write_text(json.dumps(dict(declaration_source=str(p),source_sha256=hashlib.sha256(decl.encode()).hexdigest(),only_body_changes=['composition_parts -> explicit composition argument','equality_value -> explicit equality argument'],proof_claim='conditional source-continuation model only; exact native source interpretation remains separately required'),indent=2)+'\n')

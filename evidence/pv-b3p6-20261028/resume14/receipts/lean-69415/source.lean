import PV_B3P_SelectedCorrected14227
import PV_B3P_RootGroup14227
import PV_B3P_ClosureLinks14227
import PV_B3P_MatrixStore14227
namespace PV_B3P_Groups14227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_227 PV_B3P_TopDown13227 PV_B3P_Binding13227 PV_B3P_Groups13227 PV_B3P_Correct14227
set_option autoImplicit false
noncomputable section
structure AllPorts14 (base : ExternalTypes) {ι : Type} (Sig : ι → Type) where
  bodies : ChangedBodies13
  root : RootPorts14 base
  called : U16 → Prop
  constructor : Usize → SelectorFn
  blocks : Usize
  stores : Store14
  matrix : PV_B3P_Binding14227.Matrix14 → Usize → Usize → U64 → Result PV_B3P_Binding14227.Matrix14
  slice : SliceFn14
  std : (i : ι) → Sig i

structure AllLinks14 (base : ExternalTypes) {ι : Type} (Sig : ι → Type)
    (ops : @ExternalFuns (PV_B3P_Install227.Types base))
    (ports : AllPorts14 base Sig) (stdModel : (i : ι) → Sig i) : Prop where
  terminal_qm31 : PV_B3P_Link_terminal_qm31 base ops (source_ports13 base ports.bodies.body6 ports.bodies.body7)
  missing_bodies : RootLinks14 base (source_ports13 base ports.bodies.body6 ports.bodies.body7) ports.root
  changed_functions : CorrectedLinks14 ports.bodies ports.called ports.constructor ports.blocks
  D188 : PV_B3P_Link_D188 ports.stores
  matrix : PV_B3P_Binding14227.PV_B3P_Link_matrix_stores ports.matrix
  slice : PV_B3P_Link_slice14 ports.slice
  std_dependencies : PV_B3P_Link_std_dependency_closure14 Sig ports.std stdModel

section
variable (base : ExternalTypes)
local notation "terminal" => transported_reference base
/-- All requested groups in a single typed schema. No native interpretation or
exhaustive source-cone catalogue is inferred from this conditional theorem. -/
theorem selected_all_groups14 {ι : Type} (Sig : ι → Type)
    (ops : @ExternalFuns (PV_B3P_Install227.Types base))
    (ports : AllPorts14 base Sig) (stdModel : (i : ι) → Sig i)
    (links : AllLinks14 base Sig ops ports stdModel)
    (self : @host_semantic.SemanticOracle (PV_B3P_Install227.Types base))
    (point : Array ProverRwFull.aspis_core.field.QM31 10#usize) :
    letI : ExternalTypes := PV_B3P_Install227.Types base
    ∀ claims,
      ops.op227 self.«public» claims point self.challenges =
        terminal self.«public» claims point self.challenges := by
  letI : ExternalTypes := PV_B3P_Install227.Types base
  exact selected_callback14 base ops ports.bodies ports.called ports.constructor ports.blocks
    links.terminal_qm31 links.changed_functions self point
end

def all_model14 (base : ExternalTypes) {ι : Type} (Sig : ι → Type)
    (stdModel : (i : ι) → Sig i) (append : AppendWord13) : AllPorts14 base Sig where
  bodies := corrected_model_bodies14
  root := root_model14 base append
  called := frozen_calls14
  constructor := constructor14
  blocks := 57#usize
  stores := borrowed_store14
  matrix := PV_B3P_Binding14227.source_matrix_store14
  slice := @slice_loop13 Four14
  std := stdModel

/-- Every link holds jointly for one explicit model instance, on the original
carrier, for any typed pinned dependency catalogue supplied to the schema. -/
theorem all_groups_joint_witness14 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base))
    {ι : Type} (Sig : ι → Type) (stdModel : (i : ι) → Sig i) (append : AppendWord13) :
    AllLinks14 base Sig (PV_B3P_Install227.actual base original)
      (all_model14 base Sig stdModel append) stdModel where
  terminal_qm31 := by
    intro p claims point c
    exact Eq.trans (PV_B3P_Install227.actual_source base original p claims point c)
      (continuation_composes base
        (source_ports13 base reference_terminal.composition_parts reference_terminal.equality_value)
        (semantic_source_binding13 base) source_selection_binding13
        (parts_link13 _ _ rfl rfl) p claims point c).symm
  missing_bodies := root_joint_witness14 base append _ _
  changed_functions := corrected_links_witness14
  D188 := borrowed_store_binding14
  matrix := PV_B3P_Binding14227.matrix_stores_link14
  slice := slice_model_binding14
  std_dependencies := fun _ => rfl
#print axioms selected_all_groups14
#print axioms all_groups_joint_witness14
end
end PV_B3P_Groups14227

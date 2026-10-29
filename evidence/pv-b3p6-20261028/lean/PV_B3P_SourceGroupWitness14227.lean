import PV_B3P_AllGroups14227
import PV_B3P_FieldsIterator14227
import PV_B3P_TransitionLoan14227
namespace PV_B3P_Groups14227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_Binding13227 PV_B3P_TopDown13227
set_option autoImplicit false
noncomputable section
/-- The joint model now uses the interpreted source while loop for fields,
rather than choosing its target function directly. Append is still explicit. -/
def all_source_model14 (base : ExternalTypes) {ι : Type} (Sig : ι → Type)
    (stdModel : (i : ι) → Sig i) (append : AppendWord13) : AllPorts14 base Sig :=
  { all_model14 base Sig stdModel append with
    root := { root_model14 base append with fields := PV_B3P_Fields14227.fields_source14 append } }

theorem source_groups_joint_witness14 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base))
    {ι : Type} (Sig : ι → Type) (stdModel : (i : ι) → Sig i) (append : AppendWord13) :
    AllLinks14 base Sig (PV_B3P_Install227.actual base original)
      (all_source_model14 base Sig stdModel append) stdModel := by
  have old := all_groups_joint_witness14 base original Sig stdModel append
  constructor
  · exact old.terminal_qm31
  · constructor
    · exact (root_joint_witness14 base append _ _).private_public
    · exact (root_joint_witness14 base append _ _).withdrawal_public
    · rfl
    · exact PV_B3P_Fields14227.fields_source_link14 append
    · intro out values; rfl
    · exact (root_joint_witness14 base append _ _).semantic
  · exact old.changed_functions
  · exact old.D188
  · exact old.matrix
  · exact old.slice
  · exact old.std_dependencies
#print axioms source_groups_joint_witness14
end
end PV_B3P_Groups14227

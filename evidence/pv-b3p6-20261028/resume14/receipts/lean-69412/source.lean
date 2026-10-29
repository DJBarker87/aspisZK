import PV_B3P_ScalarSemanticBinding13227
import PV_B3P_FrontierModel13227
namespace PV_B3P_Groups14227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227 PV_B3P_Binding13227
set_option autoImplicit false
noncomputable section
structure RootPorts14 (base : ExternalTypes) where
  private_public : PV_B3P_ScalarBinding13227.PP → PV_B3P_ScalarBinding13227.Late base → Result SP
  withdrawal_public : PV_B3P_ScalarBinding13227.PW → PV_B3P_ScalarBinding13227.Late base → Result SP
  transition : Public base → Result (PV_B3P_ScalarBinding13227.Late base)
  append : AppendWord13
  fields : List U8 → List U32 → Result FieldState13
  frontier : List U8 → Array (Array U32 8#usize) 20#usize → Result FieldState13

def PV_B3P_Link_private_public14 (base : ExternalTypes) (root : RootPorts14 base) : Prop :=
  ∀ p t, root.private_public p t = .ok (PV_B3P_Carrier227.semantic base (.Transfer p t))
def PV_B3P_Link_withdrawal_public14 (base : ExternalTypes) (root : RootPorts14 base) : Prop :=
  ∀ p t, root.withdrawal_public p t = .ok (PV_B3P_Carrier227.semantic base (.Withdrawal p t))
def PV_B3P_Link_transition14 (base : ExternalTypes) (root : RootPorts14 base) : Prop :=
  root.transition = PV_B3P_ScalarBinding13227.transition_source13 base

structure RootLinks14 (base : ExternalTypes) (ports : SourcePorts base)
    (root : RootPorts14 base) : Prop where
  private_public : PV_B3P_Link_private_public14 base root
  withdrawal_public : PV_B3P_Link_withdrawal_public14 base root
  transition : PV_B3P_Link_transition14 base root
  fields : PV_B3P_Link_fields root.append root.fields
  frontier : PV_B3P_Link_frontier root.append root.frontier
  semantic : PV_B3P_Link_semantic base ports
-- terminal_qm31 is the seventh root, separately typed with actual ops in the skeleton.
def root_model14 (base : ExternalTypes) (append : AppendWord13) : RootPorts14 base :=
  ⟨PV_B3P_ScalarBinding13227.private_public13 base,
   PV_B3P_ScalarBinding13227.withdrawal_public13 base,
   PV_B3P_ScalarBinding13227.transition_source13 base,append,fields_model13 append,
   fun out values => frontier_rows13 append out (values.val.map (fun row => row.val))⟩

theorem root_joint_witness14 (base : ExternalTypes) (append : AppendWord13)
    (composition : CompositionFn13) (equality : Array SQ 10#usize → Array SQ 10#usize → Result SQ) :
    RootLinks14 base (source_ports13 base composition equality) (root_model14 base append) where
  private_public := PV_B3P_ScalarBinding13227.private_public_binding13 base
  withdrawal_public := PV_B3P_ScalarBinding13227.withdrawal_public_binding13 base
  transition := rfl
  fields := rfl
  frontier := fun _ _ => rfl
  semantic := semantic_source_binding13 base
#print axioms root_joint_witness14
end
end PV_B3P_Groups14227

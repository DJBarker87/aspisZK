import PV_B3_MaskRowExpected
import R1Z.PV_CBM_MasksSelection
namespace PV_B3_MaskDictionary134
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false
abbrev NewError :=
  PV_B3_Forest_134.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1
abbrev OldError :=
  PV_CBM_ReferenceRaw.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1
abbrev NewFinal := core.result.Result (Array U16 64#usize) NewError
abbrev OldFinal := core.result.Result (Array U16 64#usize) OldError

def error : NewError → OldError
  | .Shape => .Shape
  | .EndpointCapacity row => .EndpointCapacity row

def translate : Result NewFinal → Result OldFinal
  | .ok (.Ok m) => .ok (.Ok m)
  | .ok (.Err e) => .ok (.Err (error e))
  | .fail e => .fail e
  | .div => .div

theorem copy_reference :
    translate PV_B3_Forest_134.host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 =
      PV_CBM_ReferenceRaw.reference.masks := by
  rw [PV_B3_MaskRowExpected.op134_value, R1Z.PV_Op134_Masks.source]
  rfl

noncomputable def selected (base : ExternalTypes)
    (ops : @ExternalFuns (R1Z.PV_CBM_MasksSelection.Types base)) :
    @ExternalFuns (R1Z.PV_CBM_MasksSelection.Types base) :=
  letI : ExternalTypes := R1Z.PV_CBM_MasksSelection.Types base
  {ops with op134 := (translate
    PV_B3_Forest_134.host_forest.pool_v1_pair_forest_copy_active_row_masks_v1)}

theorem dictionary (base : ExternalTypes)
    (ops : @ExternalFuns (R1Z.PV_CBM_MasksSelection.Types base)) :
    selected base ops = R1Z.PV_CBM_MasksSelection.selected base ops := by
  unfold selected R1Z.PV_CBM_MasksSelection.selected
  rw [copy_reference]

theorem op134 (base : ExternalTypes)
    (ops : @ExternalFuns (R1Z.PV_CBM_MasksSelection.Types base)) :
    @ExternalFuns.op134 (R1Z.PV_CBM_MasksSelection.Types base) (selected base ops) =
      ok (.Ok R1Z.PV_Op134_Masks.masks) := by
  rw [dictionary, R1Z.PV_CBM_MasksSelection.op134_reference,
    R1Z.PV_Op134_Masks.source]

theorem nonvacuity : ∃ m : Array U16 64#usize,
    translate PV_B3_Forest_134.host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 =
      ok (.Ok m) ∧ m.val.length = 64 := by
  exact ⟨R1Z.PV_Op134_Masks.masks, by rw [copy_reference, R1Z.PV_Op134_Masks.source],
    R1Z.PV_Op134_Masks.length⟩

theorem fail_tag (e : Aeneas.Std.Error) : translate (.fail e) = .fail e := rfl
theorem div_tag : translate .div = .div := rfl

#print axioms error
#print axioms translate
#print axioms copy_reference
#print axioms selected
#print axioms dictionary
#print axioms op134
#print axioms nonvacuity
#print axioms fail_tag
#print axioms div_tag
end PV_B3_MaskDictionary134

import PV_B3_MaskRowExpected
import R1Z.PV_Op134_MaskSpec
namespace PV_B3_MaskRowBridge
open Aeneas Aeneas.Std Result
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

theorem fail_tag (e : Aeneas.Std.Error) : translate (.fail e) = .fail e := rfl
theorem div_tag : translate .div = .div := rfl
theorem error_tag (e : NewError) : translate (.ok (.Err e)) = .ok (.Err (error e)) := rfl

-- Complete Result copy-emission/reference bridge. Native original/copy
-- source association and deployment adoption remain separate obligations.
theorem op134_source :
    translate PV_B3_Forest_134.host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 =
      PV_CBM_ReferenceRaw.reference.masks := by
  rw [PV_B3_MaskRowExpected.op134_value, R1Z.PV_Op134_Masks.source]
  rfl

theorem row_bits (block : Fin 64) (bit : Fin 16) :
    ∃ m : Array U16 64#usize,
      PV_B3_Forest_134.host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 = ok (.Ok m) ∧
      m.val.length = 64 ∧
      (Nat.testBit (m.val[block.val]'(by
        rw [m.property]; exact block.isLt)).val bit.val = true ↔
        16*block.val+bit.val ∈ R1Z.PV_Op134_RowSpec.rows.map (fun r => r.val)) := by
  exact ⟨R1Z.PV_Op134_Masks.masks, PV_B3_MaskRowExpected.op134_value,
    R1Z.PV_Op134_Masks.length, R1Z.PV_Op134_MaskSpec.bits block bit⟩

#print axioms error
#print axioms translate
#print axioms fail_tag
#print axioms div_tag
#print axioms error_tag
#print axioms op134_source
#print axioms row_bits
end PV_B3_MaskRowBridge

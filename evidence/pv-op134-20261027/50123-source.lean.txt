import R1Z.PV_CBM_CallbackBundle
import R1Z.PV_Op134_MaskSpec
import R1Z.PV_Op134_InventoryCallback
namespace R1Z.PV_Op134_ReferenceBundle
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false
noncomputable section

theorem op134_reference (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBM_CallbackBundle.Types base)) :
    @ExternalFuns.op134 (PV_CBM_CallbackBundle.Types base)
      (PV_CBM_CallbackBundle.selected base ops) = ok (.Ok PV_Op134_Masks.masks) := by
  rw [PV_CBM_CallbackBundle.op134_reference,PV_Op134_Masks.source]

theorem rows_reference (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBM_CallbackBundle.Types base)) :
    ∃ result : alloc.vec.Vec U16,
      @ExternalFuns.op133 (PV_CBM_CallbackBundle.Types base)
        (PV_CBM_CallbackBundle.selected base ops) = ok (.Ok result) ∧
      result.val = PV_Op134_RowSpec.rows ∧ result.val.length = 214 ∧
      result.val.Nodup ∧ result.val.Pairwise (fun a b => a.val < b.val) ∧
      (∀ block : Fin 64, ∀ bit : Fin 16,
        Nat.testBit (PV_Op134_Masks.masks.val[block.val]'(by
          rw [PV_Op134_Masks.length]; exact block.isLt)).val bit.val = true ↔
          16*block.val+bit.val ∈ result.val.map (fun r => r.val)) := by
  obtain ⟨result,hr,hv⟩ := PV_Op134_RowSpec.callback
  refine ⟨result,?_,hv,?_,?_,?_,?_⟩
  · rw [PV_CBM_CallbackBundle.op133_reference,hr]
  · simpa only [hv] using PV_Op134_RowSpec.length
  · simpa only [hv] using PV_Op134_RowOrder.nodup
  · simpa only [hv] using PV_Op134_RowOrder.sorted
  · simpa only [hv] using PV_Op134_MaskSpec.bits

theorem cells_reference (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBM_CallbackBundle.Types base)) :
    ∃ result : alloc.vec.Vec PV_Op134_Order.Cell,
      @ExternalFuns.op132 (PV_CBM_CallbackBundle.Types base)
        (PV_CBM_CallbackBundle.selected base ops) = ok (.Ok result) ∧
      result.val = PV_CBM_CellsSpec.literals ∧ result.val.length = 3803 ∧
      result.val.Nodup ∧
      (∀ row column : Nat, row < 1024 → column < 16 →
        PV_CBM_InventoryShape.free row column →
        ∃ c ∈ result.val, c.row.val = row ∧ c.column.val = column) := by
  obtain ⟨result,hr,hv,hl,hn,_,hc⟩ := PV_Op134_InventoryCallback.callback
  refine ⟨result,?_,hv,hl,hn,hc⟩
  rw [PV_CBM_CallbackBundle.op132_reference,hr]

#print axioms cells_reference
#print axioms op134_reference
#print axioms rows_reference
end
end R1Z.PV_Op134_ReferenceBundle

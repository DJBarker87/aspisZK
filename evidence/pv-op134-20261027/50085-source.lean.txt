import R1Z.PV_Op134_Inventory
namespace R1Z.PV_Op134_InventoryCallback
open Aeneas Aeneas.Std Result PV_Op134_Order
set_option autoImplicit false

theorem callback : ∃ result : alloc.vec.Vec Cell,
    PV_CBM_CellsMaterializer.callback = ok (.Ok result) ∧
    result.val = PV_CBM_CellsSpec.literals ∧ result.val.length = 3803 ∧
    result.val.Nodup ∧
    (∀ c ∈ result.val, c.row.val < 1024 ∧ c.column.val < 16 ∧
      PV_CBM_InventoryShape.free c.row.val c.column.val) ∧
    (∀ row column : Nat, row < 1024 → column < 16 →
      PV_CBM_InventoryShape.free row column →
      ∃ c ∈ result.val, c.row.val = row ∧ c.column.val = column) := by
  obtain ⟨result,hr,hv⟩ := PV_CBM_CellsSpec.fill (alloc.vec.Vec.new Cell)
    (by change 0+3803≤4096; decide)
  have he : result.val = PV_CBM_CellsSpec.literals := by
    simpa only [alloc.vec.Vec.new,List.nil_append] using hv
  refine ⟨result,?_,he,?_,?_,?_,?_⟩
  · unfold PV_CBM_CellsMaterializer.callback
    rw [hr]
    rfl
  · rw [he]; exact PV_CBM_CellsSpec.length
  · rw [he]; exact PV_Op134_Inventory.nodup
  · rw [he]
    intro c hc
    have hb := PV_Op134_Inventory.ordered_bounds.2 c hc
    exact ⟨hb.2.2.1,hb.2.2.2,PV_CBM_CellsSpec.all_free c hc⟩
  · rw [he]
    exact PV_Op134_Inventory.complete
#print axioms callback
end R1Z.PV_Op134_InventoryCallback

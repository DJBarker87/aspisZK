import R1Z.PV_CBM_PaddingBijection
import R1Z.PV_CBM_PathBijection
import R1Z.PV_CBM_ValueBijection
import Mathlib.Data.Fintype.Sum
namespace R1Z.PV_CBM_InventoryCardinality
open PV_CBM_InventoryShape
set_option autoImplicit false
abbrev Cell := {cell : Fin 1024 × Fin 16 // free cell.1.val cell.2.val}
abbrev Regions := PV_CBM_PaddingBijection.Cell ⊕
  (PV_CBM_PathBijection.Cell ⊕ PV_CBM_ValueBijection.Cell)
noncomputable instance : Fintype Cell := Fintype.ofFinite Cell

def toRegion (cell : Cell) : Regions :=
  if h0 : cell.val.1.val < 912 then
    Sum.inl ⟨cell.val,h0,cell.prop⟩
  else if h1 : cell.val.1.val < 1008 then
    Sum.inr (Sum.inl ⟨cell.val,⟨by omega,h1⟩,cell.prop⟩)
  else Sum.inr (Sum.inr ⟨cell.val,by omega,cell.prop⟩)

def fromRegion (region : Regions) : Cell :=
  match region with
  | Sum.inl cell => ⟨cell.val,cell.prop.2⟩
  | Sum.inr (Sum.inl cell) => ⟨cell.val,cell.prop.2⟩
  | Sum.inr (Sum.inr cell) => ⟨cell.val,cell.prop.2⟩

theorem left_inverse (cell : Cell) : fromRegion (toRegion cell) = cell := by
  unfold toRegion
  split_ifs <;> rfl

theorem right_inverse (region : Regions) : toRegion (fromRegion region) = region := by
  rcases region with cell | (cell | cell)
  · dsimp [fromRegion,toRegion]
    rw [dif_pos cell.prop.1]
  · have h0 : ¬ cell.val.1.val < 912 := by have h := cell.prop.1; omega
    dsimp [fromRegion,toRegion]
    rw [dif_neg h0,dif_pos cell.prop.1.2]
  · have h0 : ¬ cell.val.1.val < 912 := by have h := cell.prop.1; omega
    have h1 : ¬ cell.val.1.val < 1008 := by have h := cell.prop.1; omega
    dsimp [fromRegion,toRegion]
    rw [dif_neg h0,dif_neg h1]

def equiv : Cell ≃ Regions :=
  ⟨toRegion,fromRegion,left_inverse,right_inverse⟩

theorem cardinal : Fintype.card Cell = 3803 := by
  rw [Fintype.card_congr equiv]
  simp only [Regions,Fintype.card_sum,PV_CBM_PaddingBijection.cardinal,
    PV_CBM_PathBijection.cardinal,PV_CBM_ValueBijection.cardinal]

#print axioms left_inverse
#print axioms right_inverse
#print axioms cardinal
end R1Z.PV_CBM_InventoryCardinality

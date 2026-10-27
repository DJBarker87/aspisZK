import RPu_AspisR1_PoseidonPreparedIndexProductBounds
import AspisV8R15.ExactTowerBase

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedProductCast
open Aeneas.Std AspisV8R15.ExactTowerBase

abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev PreparedArray := AspisR1PoseidonPreparedIndexProductBounds.PreparedArray
abbrev Components := AspisR1PoseidonPreparedIndexProductBounds.Components
abbrev M31 := AspisR1SelectedMaskProbe.field.M31

private def at3 {α : Type} (a : Array α 3#usize) (i : Usize) (hi : i.val < 3) : α :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3 a i hi

private def leftCell (left : PreparedArray) (index component channel : Usize)
    (hi : index.val < 3) (hc : component.val < 3) (hch : channel.val < 3) : M31 :=
  at3 (at3 (at3 left index hi).components component hc) channel hch

private def tableCell (table : Components) (component channel : Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : M31 :=
  at3 (at3 table component hc) channel hch

 theorem product_cast_eq (left : PreparedArray) (tables : Fin 3 → Components)
    (i : Fin 3) (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3)
    (a b : M31)
    (hleft : leftCell left
      (AspisR1PoseidonPreparedIndexProductBounds.uFin i) c ch
      (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt) hc hch = a)
    (hright : tableCell (tables i) c ch hc hch = b) :
    ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i c ch hc hch : Nat) : M) =
      (a.val : M) * (b.val : M) := by
  unfold AspisR1PoseidonPreparedIndexProductBounds.product
  rw [Nat.cast_mul]
  change ((leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) c ch
      (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt) hc hch).val *
    (tableCell (tables i) c ch hc hch).val : M) = (a.val : M) * (b.val : M)
  rw [hleft, hright]

#print axioms product_cast_eq
end AspisR1.PoseidonPreparedProductCast

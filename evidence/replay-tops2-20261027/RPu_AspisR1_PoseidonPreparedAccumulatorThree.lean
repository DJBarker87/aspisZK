import RPu_AspisR1_PoseidonPreparedPrefixFieldThree
import RPu_AspisR1PoseidonPreparedIndexActualLoopBuild

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedAccumulatorThree
open Aeneas.Std AspisV8R15.ExactTowerBase

abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev PreparedArray := AspisR1PoseidonPreparedIndexProductBounds.PreparedArray
abbrev Components := AspisR1PoseidonPreparedIndexProductBounds.Components
abbrev Sums := AspisR1PoseidonPreparedIndexActualLoopBuild.Sums
abbrev Usize := Aeneas.Std.Usize

theorem accumulator_cell_three (left : PreparedArray) (tables : Fin 3 → Components)
    (sums : Sums)
    (hvalues : ∀ (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3),
      ((AspisR1PoseidonPreparedIndexActualLoopBuild.sumCell sums c ch hc hch).val : M) =
        AspisR1PoseidonPreparedIndexProductBounds.prefixProduct left tables 3 c ch hc hch)
    (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3) :
    ((AspisR1PoseidonPreparedIndexActualLoopBuild.sumCell sums c ch hc hch).val : M) =
      ((AspisR1PoseidonPreparedIndexProductBounds.product left tables ⟨0, by omega⟩ c ch hc hch : Nat) : M) +
      ((AspisR1PoseidonPreparedIndexProductBounds.product left tables ⟨1, by omega⟩ c ch hc hch : Nat) : M) +
      ((AspisR1PoseidonPreparedIndexProductBounds.product left tables ⟨2, by omega⟩ c ch hc hch : Nat) : M) := by
  rw [hvalues, AspisR1.PoseidonPreparedPrefixField.prefixProduct_cast]
  rw [AspisR1.PoseidonPreparedPrefixFieldThree.prefixField_three]
  rfl

#print axioms accumulator_cell_three
end AspisR1.PoseidonPreparedAccumulatorThree

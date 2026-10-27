import RPv_AspisR1_PoseidonPreparedPrefixField

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedPrefixFieldThree
open Aeneas.Std AspisV8R15.ExactTowerBase

abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev Usize := Aeneas.Std.Usize

private def i0 : Fin 3 := ⟨0, by omega⟩
private def i1 : Fin 3 := ⟨1, by omega⟩
private def i2 : Fin 3 := ⟨2, by omega⟩

theorem prefixField_succ (left : AspisR1PoseidonPreparedIndexProductBounds.PreparedArray)
    (tables : Fin 3 → AspisR1PoseidonPreparedIndexProductBounds.Components)
    (n : Nat) (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3) :
    AspisR1.PoseidonPreparedPrefixField.prefixField left tables (Nat.succ n) c ch hc hch =
      AspisR1.PoseidonPreparedPrefixField.prefixField left tables n c ch hc hch +
        ((AspisR1PoseidonPreparedIndexProductBounds.product left tables
          ⟨n % 3, Nat.mod_lt _ (by omega)⟩ c ch hc hch : Nat) : M) := by
  rfl

theorem prefixField_three (left : AspisR1PoseidonPreparedIndexProductBounds.PreparedArray)
    (tables : Fin 3 → AspisR1PoseidonPreparedIndexProductBounds.Components)
    (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3) :
    AspisR1.PoseidonPreparedPrefixField.prefixField left tables 3 c ch hc hch =
      ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i0 c ch hc hch : Nat) : M) +
      ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i1 c ch hc hch : Nat) : M) +
      ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i2 c ch hc hch : Nat) : M) := by
  change AspisR1.PoseidonPreparedPrefixField.prefixField left tables
      (Nat.succ (Nat.succ (Nat.succ 0))) c ch hc hch = _
  rw [prefixField_succ, prefixField_succ, prefixField_succ]
  simp [AspisR1.PoseidonPreparedPrefixField.prefixField,
    AspisR1PoseidonPreparedIndexProductBounds.product,
    AspisR1PoseidonPreparedIndexProductBounds.uFin, i0, i1, i2]

#print axioms prefixField_succ
#print axioms prefixField_three
end AspisR1.PoseidonPreparedPrefixFieldThree

import RPu_AspisR1.PoseidonPreparedIndexProductBounds
import AspisV8R15.ExactTowerBase

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedPrefixField
open Aeneas.Std AspisR1PoseidonPreparedIndexProductBounds

abbrev M := AspisV8R15.ExactTowerBase.M31Exact

def prefixField (left : PreparedArray) (tables : Fin 3 → Components)
    (count : Nat) (component channel : Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : M :=
  Nat.rec 0
    (fun n acc => acc + (product left tables ⟨n % 3, Nat.mod_lt _ (by omega)⟩
      component channel hc hch : M)) count

theorem prefixProduct_cast (left : PreparedArray) (tables : Fin 3 → Components)
    (count : Nat) (component channel : Usize)
    (hc : component.val < 3) (hch : channel.val < 3) :
    (prefixProduct left tables count component channel hc hch : M) =
      prefixField left tables count component channel hc hch := by
  induction count with
  | zero => rfl
  | succ n ih =>
      simp only [prefixProduct_succ, prefixField, ih, Nat.cast_add]

#print axioms prefixProduct_cast
end AspisR1.PoseidonPreparedPrefixField

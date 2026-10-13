import AspisV8R15.ExactTowerBase

/-! Finite instances and cardinalities for the retained exact tower.

This module deliberately contains only finite-set bookkeeping. The field
definitions and rootless proofs live in `ExactTowerBase`, which has a small
import footprint independent of the legacy sampler and hiding development.
-/
set_option autoImplicit false
namespace AspisV8R15.ExactTowerFinite
open AspisV8R15.ExactTowerBase

noncomputable instance cm31ExactFintype : Fintype CM31Exact :=
  Fintype.ofEquiv (M31Exact × M31Exact)
    (QuadraticAlgebra.equivProd (-1) 0).symm

noncomputable instance qm31ExactFintype : Fintype QM31Exact :=
  Fintype.ofEquiv (CM31Exact × CM31Exact)
    (QuadraticAlgebra.equivProd qm31R 0).symm

theorem cm31Exact_card : Fintype.card CM31Exact = P ^ 2 := by
  calc
    Fintype.card CM31Exact = Fintype.card (M31Exact × M31Exact) :=
      Fintype.card_congr (QuadraticAlgebra.equivProd (-1) 0)
    _ = P * P := by rw [Fintype.card_prod, ZMod.card]
    _ = P ^ 2 := by rw [pow_two]

theorem qm31Exact_card : Fintype.card QM31Exact = P ^ 4 := by
  calc
    Fintype.card QM31Exact = Fintype.card (CM31Exact × CM31Exact) :=
      Fintype.card_congr (QuadraticAlgebra.equivProd qm31R 0)
    _ = P ^ 2 * P ^ 2 := by rw [Fintype.card_prod, cm31Exact_card]
    _ = P ^ 4 := by rw [← pow_add]

#print axioms cm31Exact_card
#print axioms qm31Exact_card
end AspisV8R15.ExactTowerFinite

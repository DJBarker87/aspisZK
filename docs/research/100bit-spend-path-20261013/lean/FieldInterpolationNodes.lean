import Mathlib.Algebra.CharP.Basic

namespace AspisWide.FieldInterpolationNodes
variable {K : Type} [Ring K]

/-- Public deterministic nodes; no search or field enumeration is used. -/
def nodes (n : Nat) : Fin n → K := fun i => (i.val : K)

theorem nodes_injective {p n : Nat} [CharP K p] (hn : n < p) :
    Function.Injective (nodes (K := K) n) := by
  intro i j h
  apply Fin.ext
  exact CharP.natCast_injOn_Iio K p
    (lt_trans i.isLt hn) (lt_trans j.isLt hn) h

theorem nodes_avoid_neg_one {p n : Nat} [CharP K p] (hn : n < p) :
    ∀ i, nodes (K := K) n i ≠ -1 := by
  intro i h
  have hz : ((i.val+1 : Nat) : K) = 0 := by
    rw [Nat.cast_add, Nat.cast_one]
    change nodes (K := K) n i + 1 = 0
    rw [h, neg_add_cancel]
  have hd : p ∣ i.val+1 := (CharP.cast_eq_zero_iff K p _).mp hz
  have hle := Nat.le_of_dvd (Nat.succ_pos i.val) hd
  have hlt : i.val+1 < p := lt_of_le_of_lt (Nat.succ_le_of_lt i.isLt) hn
  exact (not_le_of_gt hlt) hle


#print axioms nodes
#print axioms nodes_injective
#print axioms nodes_avoid_neg_one
end AspisWide.FieldInterpolationNodes

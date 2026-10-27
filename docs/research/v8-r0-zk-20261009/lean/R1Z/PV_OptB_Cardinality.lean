import R1Z.PV_OptB_Pigeonhole
import R1Z.PV_OptB_WitnessFamily
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_Cardinality
open R0P AspisR1.SpendRelation R1Z.BuilderSpendRelation PV_OptB_WitnessFamily

/-- The sixteen-coordinate family has collisions in its eight-coordinate
public root. No concrete Poseidon recurrence is evaluated. This is not yet
a pair whose native failure observations differ. -/
theorem same_public_distinct_witnesses {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [CharP K 2147483647] (pub : Public K) (w : Witness K) (valid : RspendPlus pub w) :
    ∃ t u : Fin 16 → K,
      publicInput pub w t = publicInput pub w u ∧ witness w t ≠ witness w u ∧
      RspendPlus (publicInput pub w t) (witness w t) ∧
      RspendPlus (publicInput pub w u) (witness w u) := by
  classical
  have collide : ∃ t u : Fin 16 → K, root pub w t = root pub w u ∧ t ≠ u := by
    by_contra absent
    have injective : Function.Injective (root pub w) := by
      intro t u same
      by_contra different
      exact absent ⟨t,u,same,different⟩
    have card := Fintype.card_le_of_injective (root pub w) injective
    have nontrivial : 1 < Fintype.card K := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    have powers : Fintype.card K ^ 8 < Fintype.card K ^ 16 :=
      Nat.pow_lt_pow_right nontrivial (by decide)
    have domain : Fintype.card (Fin 16 → K) = Fintype.card K ^ 16 := by simp
    have range : Fintype.card (Digest K) = Fintype.card K ^ 8 := by simp [Digest]
    rw [domain,range] at card
    exact (not_lt_of_ge card) powers
  obtain ⟨t,u,same,different⟩ := collide
  refine ⟨t,u,public_eq_of_root_eq pub w t u same,?_,rspendPlus pub w valid t,rspendPlus pub w valid u⟩
  intro equal
  exact different (witness_injective w equal)

/-- Numerical shape used by the sparse-set obstruction: no large trace or
field enumeration occurs. The only literal comparison is 4096² < p. -/
theorem sparse_cardinality :
    (2147483647 : Nat)^8 * 4096^16 < 2147483647^16 := by
  have small : (4096 : Nat)^2 < 2147483647 := by norm_num
  have raised : ((4096 : Nat)^2)^8 < 2147483647^8 :=
    Nat.pow_lt_pow_left small (by decide)
  have positive : 0 < (2147483647 : Nat)^8 := by positivity
  calc
    _ = (2147483647 : Nat)^8 * ((4096 : Nat)^2)^8 := by rw [← pow_mul]
    _ < (2147483647 : Nat)^8 * 2147483647^8 := Nat.mul_lt_mul_of_pos_left raised positive
    _ = 2147483647^16 := by rw [← pow_add]

#print axioms same_public_distinct_witnesses
#print axioms sparse_cardinality
end R1Z.PV_OptB_Cardinality

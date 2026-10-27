import Lean
namespace R1Z.PV_Canon
 theorem block_index (j k : Nat) (hj : j < 7) (hk : k < 4) : 4*j+k < 28 := by omega
 theorem block_decomposition (i : Nat) (hi : i < 28) :
    i / 4 < 7 ∧ i % 4 < 4 ∧ 4 * (i / 4) + i % 4 = i := by omega
 theorem sample_constructor_bound (i : Nat) (hi : i < 28) : i < 2147483647 := by omega
 theorem round_challenge_row (r : Nat) (hr : r < 10) : 15+r ≤ 24 := by omega
 theorem interpolation_predecessor (k : Nat) (hk : 0 < k) (hb : k < 28) : k-1 < 28 := by omega
#print axioms block_index
#print axioms block_decomposition
#print axioms sample_constructor_bound
#print axioms round_challenge_row
#print axioms interpolation_predecessor
end R1Z.PV_Canon

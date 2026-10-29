import Mathlib.Tactic
set_option autoImplicit false
namespace NDL_ChannelBounds
abbrev P : Nat := 2147483647
abbrev B : Nat := (P-1)*(P-1)

theorem product (x y : Nat) (hx : x<P) (hy : y<P) : x*y≤B := by
  exact Nat.mul_le_mul (by omega) (by omega)

theorem cell (count sum x y : Nat) (hc : count<4) (hs : sum≤count*B)
    (hx : x<P) (hy : y<P) :
    sum+x*y≤(count+1)*B ∧ sum+x*y<2^64 := by
  have step : sum+x*y≤(count+1)*B := by
    calc
      sum+x*y ≤ count*B+B := Nat.add_le_add hs (product x y hx hy)
      _ = (count+1)*B := by ring
  have cap : (count+1)*B≤4*B := Nat.mul_le_mul_right B (by omega)
  have limit : 4*B<2^64 := by norm_num [B,P]
  exact ⟨step,lt_of_le_of_lt (le_trans step cap) limit⟩

/-- The long dot branch has at most20 canonical block replies at width80.
This is a bound lemma, not a native product or source-iteration certificate. -/
theorem outer (blocks sum reduced : Nat) (hb : blocks<20)
    (hs : sum≤blocks*(P-1)) (hr : reduced<P) :
    sum+reduced≤(blocks+1)*(P-1) ∧ sum+reduced<2^64 := by
  have step : sum+reduced≤(blocks+1)*(P-1) := by
    have : reduced≤P-1 := by omega
    nlinarith
  have cap : (blocks+1)*(P-1)≤20*(P-1) := Nat.mul_le_mul_right (P-1) (by omega)
  have limit : 20*(P-1)<2^64 := by norm_num [P]
  exact ⟨step,lt_of_le_of_lt (le_trans step cap) limit⟩

#print axioms product
#print axioms cell
#print axioms outer
end NDL_ChannelBounds

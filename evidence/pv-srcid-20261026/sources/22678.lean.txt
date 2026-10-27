import R1Z.BuilderRecordsAdmission

/-! Symbolic reconstruction of low binary digits. This lemma is generic in
both width and value; no finite input space is evaluated. -/
set_option autoImplicit false
namespace R1Z.PV_Src_LowBits

theorem sum (v n : Nat) :
    (∑ i ∈ Finset.range n, 2^i * (v / 2^i % 2)) = v % 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    let a := 2^n
    let r := v % a + a * (v / a % 2)
    have ha : 0 < a := pow_pos (by decide : 0 < (2 : Nat)) n
    have hrem : v % a < a := Nat.mod_lt _ ha
    have hbit : v / a % 2 ≤ 1 := by
      have := Nat.mod_lt (v / a) (by decide : 0 < 2)
      omega
    have hmul : a * (v / a % 2) ≤ a := by
      simpa using Nat.mul_le_mul_left a hbit
    have hr : r < a*2 := by dsimp [r]; omega
    have repr : v = (v/a/2)*(a*2)+r := by
      calc
        v = v % a + a * (v / a) := (Nat.mod_add_div v a).symm
        _ = v % a + a * (v / a % 2 + 2 * (v / a / 2)) := by
          exact congrArg (fun t : Nat => v % a + a*t)
            (Nat.mod_add_div (v/a) 2).symm
        _ = (v/a/2)*(a*2)+r := by dsimp [r]; ring
    have hz : ((v/a/2)*(a*2)) % (a*2) = 0 := by simp
    have hm : v % (a*2) = r := by
      conv_lhs => arg 1; rw [repr]
      rw [Nat.add_mod,hz,Nat.zero_add,Nat.mod_mod]
      exact Nat.mod_eq_of_lt hr
    simpa only [a,r,pow_succ] using hm.symm

#print axioms sum
end R1Z.PV_Src_LowBits

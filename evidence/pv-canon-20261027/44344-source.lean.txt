import R1Z.PV_Canon_Nat
namespace R1Z.PV_Canon
 theorem fold31_mod (x : Nat) : fold31 x % P = x % P := by
  have h := Nat.mod_add_div x 2147483648
  have decompose : fold31 x + P * (x / 2147483648) = x := by
    unfold fold31 P
    omega
  calc
    fold31 x % P = (fold31 x + P * (x / 2147483648)) % P := by
      rw [Nat.add_mod,Nat.mul_mod]
      simp
    _ = x % P := congrArg (fun y => y % P) decompose
 theorem subtractP_mod (x : Nat) : subtractP x % P = x % P := by
  unfold subtractP
  split
  · rename_i h
    calc
      (x-P)%P = ((x-P)+P)%P := (Nat.add_mod_right (x-P) P).symm
      _ = x%P := congrArg (fun y => y%P) (Nat.sub_add_cancel h)
  · rfl
 theorem reduce64_mod (x : Nat) : reduce64 x % P = x % P := by
  unfold reduce64
  rw [subtractP_mod,fold31_mod,fold31_mod]
 theorem reduce64_exact (x : Nat) (hx : x < 18446744073709551616) : reduce64 x=x%P := by
  have h := reduce64_mod x
  rw [Nat.mod_eq_of_lt (reduce64_canonical x hx)] at h
  exact h
#print axioms fold31_mod
#print axioms subtractP_mod
#print axioms reduce64_mod
#print axioms reduce64_exact
end R1Z.PV_Canon

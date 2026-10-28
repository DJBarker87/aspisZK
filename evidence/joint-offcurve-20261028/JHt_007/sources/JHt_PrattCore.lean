import JHt_BinaryModPow
import Mathlib.NumberTheory.LucasPrimality
set_option autoImplicit false
namespace AspisR1.JHt_PrattCore
open JHt_BinaryModPow

theorem cast_modPow (a e m k : Nat) (he : e < 2^k) :
    (modPow a e m k : ZMod m) = (a : ZMod m) ^ e := by
  rw [correct a e m k he]
  simp
#print axioms cast_modPow

theorem prime_mem (qs : List Nat) (hs : ∀ q ∈ qs, Nat.Prime q)
    (q : Nat) (hq : q.Prime) (hd : q ∣ qs.prod) : q ∈ qs := by
  induction qs with
  | nil => simpa using hq.not_dvd_one hd
  | cons r rs ih =>
    rcases hq.dvd_mul.mp hd with hr | ht
    · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (hs r (by simp))).mp hr))
    · exact List.mem_cons.mpr (Or.inr (ih (fun s hm => hs s (by simp [hm])) ht))
#print axioms prime_mem

theorem certificate (n a k : Nat) (hk : n - 1 < 2^k) (qs : List Nat)
    (hs : ∀ q ∈ qs, Nat.Prime q) (hf : qs.prod = n - 1)
    (h0 : modPow a (n - 1) n k = 1)
    (hqs : ∀ q ∈ qs, (modPow a ((n - 1) / q) n k : ZMod n) ≠ 1) :
    Nat.Prime n := by
  apply lucas_primality n (a : ZMod n)
  · rw [← cast_modPow a (n-1) n k hk, h0, Nat.cast_one]
  · intro q hq hd
    rw [← cast_modPow a ((n-1)/q) n k (lt_of_le_of_lt (Nat.div_le_self _ _) hk)]
    exact hqs q (prime_mem qs hs q hq (hf ▸ hd))
#print axioms certificate

/-- Single 255-bit preflight: 255 recursive calls, reduced bases. -/
theorem preflight : modPow 2 57896044618658097711785492504343953926634992332820282019728792003956564819948 57896044618658097711785492504343953926634992332820282019728792003956564819949 256 = 1 := by
  decide
#print axioms preflight
end AspisR1.JHt_PrattCore

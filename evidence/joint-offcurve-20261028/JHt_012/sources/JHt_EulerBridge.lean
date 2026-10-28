import JHt_PrattCore
import Mathlib.NumberTheory.LegendreSymbol.Basic
set_option autoImplicit false
namespace AspisR1.JHt_EulerBridge
open JHt_BinaryModPow JHt_PrattCore

/-- A checked inverse and Euler nonresidue exclude every natural square witness.
No bound on x is needed. Zero denominators/numerators cannot satisfy these checks. -/
theorem no_solution (p u v vi r : Nat) [Fact p.Prime] (hp : 2 < p)
    (hi : v * vi % p = 1) (hr : u * vi % p = r)
    (he : modPow r (p / 2) p 256 = p - 1) (hk : p / 2 < 2^256) :
    ¬ ∃ x : Nat, (v * x * x) % p = u % p := by
  have hi' : (v : ZMod p) * (vi : ZMod p) = 1 := by
    have hh := congrArg (fun n : Nat => (n : ZMod p)) hi
    simpa using hh
  have hr' : (u : ZMod p) * (vi : ZMod p) = (r : ZMod p) := by
    have hh := congrArg (fun n : Nat => (n : ZMod p)) hr
    simpa using hh
  have he' : (r : ZMod p) ^ (p / 2) = -1 := by
    rw [← cast_modPow r (p / 2) p 256 hk, he]
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    simp
  have hr0 : (r : ZMod p) ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : p / 2 ≠ 0)] at he'
    exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0) he'.symm
  rintro ⟨x, hx⟩
  have hx' : (v : ZMod p) * (x : ZMod p) * (x : ZMod p) = (u : ZMod p) := by
    have hh := congrArg (fun n : Nat => (n : ZMod p)) hx
    simpa using hh
  have hs : IsSquare (r : ZMod p) := by
    refine ⟨(x : ZMod p), ?_⟩
    calc (r : ZMod p) = (u : ZMod p) * (vi : ZMod p) := hr'.symm
      _ = ((v : ZMod p) * (x : ZMod p) * (x : ZMod p)) * (vi : ZMod p) := by rw [hx']
      _ = ((v : ZMod p) * (vi : ZMod p)) * ((x : ZMod p) * (x : ZMod p)) := by ring
      _ = (x : ZMod p) * (x : ZMod p) := by rw [hi', one_mul]
  have hh := (ZMod.euler_criterion p hr0).mp hs
  rw [he'] at hh
  have ht : (2 : ZMod p) = 0 := by linear_combination hh
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp ht
  exact (Nat.not_le_of_gt hp) (Nat.le_of_dvd (by decide) hd)
#print axioms no_solution
end AspisR1.JHt_EulerBridge

import Lean.Elab.Tactic.Omega

/-! Symbolic arithmetic for the sampler's conditional carry/reduction step.
These lemmas do not identify Rust digits or loop behavior, and make no
sampling, probability, or security claim. -/

set_option autoImplicit false
namespace AspisR1.SamplerCarry

/-- The carry branch returns `s` below the limit and otherwise subtracts the
modulus and adds one. -/
def carryResult (N q r : Nat) : Nat :=
  let s := r + q + 1
  if s < N then s else s - N + 1

theorem carry_modular_identity {N q r : Nat}
    (hN : 2 ≤ N) (hq : q < N - 1) (hr : r < N) :
    carryResult N q r = ((q * N + r) % (N - 1)) + 1 ∧
      0 < carryResult N q r ∧ carryResult N q r < N := by
  have hsum : q + r < 2 * (N - 1) := by omega
  have hmod : (q * N + r) % (N - 1) = (q + r) % (N - 1) := by
    have hN' : N = (N - 1) + 1 := by omega
    have hprod : q * N = q * (N - 1) + q := by
      calc
        q * N = q * ((N - 1) + 1) := congrArg (fun x => q * x) hN'
        _ = q * (N - 1) + q := by rw [Nat.mul_add]; simp
    have hsumEq : q * N + r = q * (N - 1) + (q + r) := by
      rw [hprod]
      omega
    calc
      (q * N + r) % (N - 1) =
          (q * (N - 1) + (q + r)) % (N - 1) := by
        rw [hsumEq]
      _ = ((q * (N - 1)) % (N - 1) + (q + r) % (N - 1)) % (N - 1) := by
        rw [Nat.add_mod]
      _ = (q + r) % (N - 1) := by simp
  have hformula : carryResult N q r = ((q * N + r) % (N - 1)) + 1 := by
    dsimp [carryResult]
    by_cases hs : r + q + 1 < N
    · rw [if_pos hs, hmod]
      have hlt : q + r < N - 1 := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega
    · rw [if_neg hs, hmod]
      have hge : N - 1 ≤ q + r := by omega
      have hsub_lt : q + r - (N - 1) < N - 1 := by omega
      have hsub_mod : (q + r) % (N - 1) = q + r - (N - 1) := by
        have hdecomp : q + r = (N - 1) + (q + r - (N - 1)) := by omega
        rw [hdecomp, Nat.add_mod]
        simp [Nat.mod_eq_of_lt hsub_lt]
      rw [hsub_mod]
      omega
  refine ⟨hformula, ?_, ?_⟩
  · rw [hformula]
    omega
  · rw [hformula]
    have hmod_lt : (q * N + r) % (N - 1) < N - 1 :=
      Nat.mod_lt _ (by omega)
    omega

/-- In the wrapped branch, subtracting the limit and then adding one still
leaves a value below `N`; there is no second carry. -/
theorem wrapped_result_lt {N q r : Nat}
    (hN : 2 ≤ N) (hq : q < N - 1) (hr : r < N)
    (hwrap : N ≤ r + q + 1) :
    r + q + 1 - N + 1 < N := by
  have hsum : q + r < 2 * (N - 1) := by omega
  omega

#print axioms carry_modular_identity
#print axioms wrapped_result_lt

end AspisR1.SamplerCarry

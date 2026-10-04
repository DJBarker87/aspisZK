import AspisV8R19.R368WireSemanticCompatibility

/-! Abstract compact-boundary rejoin diagnostic.  This file has no Rust
execution, source-degree, transcript-law, probability, privacy, or security claim. -/
set_option autoImplicit false
namespace AspisV8R19.R548

open Polynomial
open AspisV8R17
open AspisR19.R366SemanticNormalization
open AspisR19.R368WireSemanticCompatibility
open scoped BigOperators

variable {F : Type*} [Field F] [NeZero (2 : F)]

noncomputable def reconstructed (claim : F) (p : F[X]) : F[X] :=
  wirePolynomial claim (p.coeff 0) (tail p)

/-- Reconstructing all stored coefficients and changing only the omitted
linear coefficient adds the displayed linear boundary discrepancy. -/
theorem reconstructed_eval (p : F[X]) (hp : p.natDegree ≤ 27) (claim x : F) :
    (reconstructed claim p).eval x =
      p.eval x + (claim - (p.eval 0 + p.eval 1)) * x := by
  unfold reconstructed
  rw [wire_eval]
  have hx := finite_expansion p hp x
  have h0 := finite_expansion p hp 0
  have h1 := finite_expansion p hp 1
  have hs0 : (∑ i : Fin 26, tail p i * (0:F)^(i.val+2)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp
  simp only [pow_zero, zero_mul, mul_zero, one_pow, mul_one] at h0 h1
  rw [hs0] at h0
  simp only [semanticRound, roundEval]
  rw [hx]
  field_simp
  linear_combination h0 + h1

/-- Away from zero, equality of this reconstructed evaluation is exactly the
retained boundary condition. -/
theorem reconstructed_eval_eq_iff_zero
    (p : F[X]) (hp : p.natDegree ≤ 27) (claim x : F)
    (hclaim : claim ≠ p.eval 0 + p.eval 1) :
    (reconstructed claim p).eval x = p.eval x ↔ x = 0 := by
  rw [reconstructed_eval p hp claim x]
  constructor
  · intro h
    have hz : (claim - (p.eval 0 + p.eval 1)) * x = 0 := by
      linarith
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hclaim)
  · intro hx
    subst x
    simp

/-- At the zero challenge, the carried value is identical without any boundary
condition on `claim`. -/
theorem reconstructed_zero_rejoins (p : F[X]) (hp : p.natDegree ≤ 27) (claim : F) :
    (reconstructed claim p).eval 0 = p.eval 0 := by
  rw [reconstructed_eval p hp claim 0]
  ring

/-- Once the zero evaluation has rejoined, identical remaining records and
challenges make the reconstructed wire suffix definitionally identical. -/
theorem wire_suffix_rejoins
    (p : F[X]) (hp : p.natDegree ≤ 27) (claim : F) (r : Nat)
    (sent : RoundCoins (F × (Fin 26 → F)) r) (z : RoundCoins F r) :
    wireRounds r ((reconstructed claim p).eval 0) sent z =
      wireRounds r (p.eval 0) sent z := by
  rw [reconstructed_zero_rejoins p hp claim]

/-- The same rejoin makes the continuation carry identical. -/
theorem walk_suffix_rejoins
    (p : F[X]) (hp : p.natDegree ≤ 27) (claim : F) (r : Nat)
    (sent : RoundCoins (F × (Fin 26 → F)) r) (z : RoundCoins F r) :
    walk r ((reconstructed claim p).eval 0)
        (wireRounds r ((reconstructed claim p).eval 0) sent z) z =
      walk r (p.eval 0) (wireRounds r (p.eval 0) sent z) z := by
  rw [reconstructed_zero_rejoins p hp claim]

/-- Therefore the same terminal guard, including its error behavior, receives
identical continuation results. -/
theorem terminal_guard_suffix_rejoins {E : Type*} [DecidableEq F]
    (terminalError : E) (result : Except E F) (p : F[X])
    (hp : p.natDegree ≤ 27) (claim : F) (r : Nat)
    (sent : RoundCoins (F × (Fin 26 → F)) r) (z : RoundCoins F r) :
    terminalGuard terminalError result
      (walk r ((reconstructed claim p).eval 0)
        (wireRounds r ((reconstructed claim p).eval 0) sent z) z) =
    terminalGuard terminalError result
      (walk r (p.eval 0) (wireRounds r (p.eval 0) sent z) z) := by
  rw [walk_suffix_rejoins p hp claim r sent z]

#print axioms reconstructed_eval
#print axioms reconstructed_eval_eq_iff_zero
#print axioms reconstructed_zero_rejoins
#print axioms wire_suffix_rejoins
#print axioms walk_suffix_rejoins
#print axioms terminal_guard_suffix_rejoins

end AspisV8R19.R548

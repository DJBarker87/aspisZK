import R1RawFunctionalWeights

/-! Algebraic materialization of the seven weighted coefficient rows through
two linear radix-four dual folds and a final dot product. This does not assert
equality with an optimized Rust pairing implementation. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawPairing

open scoped BigOperators
variable {K E : Type} [Field K] [Field E]

/-- The dual radix-four fold is linear in its coefficient vector. -/
def dualFoldLinear {n : Nat} (alpha : E) :
    (Fin (4 * n) → E) →ₗ[E] (Fin n → E) where
  toFun w := AspisR1.RoundPairing.dualFold alpha w
  map_add' x y := by
    funext d
    simp [AspisR1.RoundPairing.dualFold, Finset.sum_add_distrib,
      add_mul]
    ring
  map_smul' c x := by
    funext d
    change AspisR1.RoundPairing.dualFold alpha (fun i => c * x i) d =
      c * AspisR1.RoundPairing.dualFold alpha x d
    unfold AspisR1.RoundPairing.dualFold
    have hsum :
        (∑ t : Fin 4,
          (c * x (AspisR1.childIndex d t)) *
            alpha ^ ((4 - t.val) % 4)) =
          c * ∑ t : Fin 4,
            x (AspisR1.childIndex d t) * alpha ^ ((4 - t.val) % 4) := by
      calc
        (∑ t : Fin 4,
            (c * x (AspisR1.childIndex d t)) *
              alpha ^ ((4 - t.val) % 4)) =
            ∑ t : Fin 4,
              c * (x (AspisR1.childIndex d t) *
                alpha ^ ((4 - t.val) % 4)) := by
          apply Finset.sum_congr rfl
          intro t ht
          ring
        _ = c * ∑ t : Fin 4,
            x (AspisR1.childIndex d t) * alpha ^ ((4 - t.val) % 4) := by
          rw [Finset.mul_sum]
    rw [hsum]
    ring

/-- Dotting with a fixed vector is linear in the second vector. -/
def dotLinear {n : Nat} (f : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun g := AspisR1.RoundPairing.dot f g
  map_add' x y := by
    simp [AspisR1.RoundPairing.dot, Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    change AspisR1.RoundPairing.dot f (fun i => c * x i) =
      c * AspisR1.RoundPairing.dot f x
    unfold AspisR1.RoundPairing.dot
    calc
      (∑ i : Fin n, f i * (c * x i)) =
          ∑ i : Fin n, c * (f i * x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c * ∑ i : Fin n, f i * x i := by
        rw [Finset.mul_sum]

/-- One raw coefficient row embedded coordinatewise into `E`. -/
def embeddedRow {n : Nat} (iota : K →+* E)
    (raw : Fin n → K) : Fin n → E :=
  fun i => iota (raw i)

theorem weights_eq_sum_embedded_rows {n : Nat} (iota : K →+* E)
    (raw : Fin 7 → Fin n → K) (kappa : E) :
    AspisR1.FunctionalWeights.weights
        (AspisR1.RawFunctionalWeights.rawFunctionals iota raw)
        (AspisR1.RawFunctionalWeights.rawBaseFunctional iota raw) kappa =
      ∑ k : Fin 7, kappa ^ k.val • embeddedRow iota (raw k) := by
  funext i
  rw [AspisR1.RawFunctionalWeights.weights_eq_raw_rows]
  simp [embeddedRow, Pi.smul_apply, smul_eq_mul]

/-- The two-fold dual pairing of the functional weights is the sum over all
seven embedded raw coefficient rows. -/
theorem two_dual_dot_eq_seven_rows
    (iota : K →+* E) (raw : Fin 7 → Fin 1024 → K) (kappa alpha0 alpha1 : E)
    (f : Fin 64 → E) :
    AspisR1.RoundPairing.dot f
        (AspisR1.RoundPairing.dualFold alpha1
          (AspisR1.RoundPairing.dualFold alpha0
            (AspisR1.FunctionalWeights.weights
              (AspisR1.RawFunctionalWeights.rawFunctionals iota raw)
              (AspisR1.RawFunctionalWeights.rawBaseFunctional iota raw) kappa))) =
      ∑ k : Fin 7, kappa ^ k.val *
        AspisR1.RoundPairing.dot f
          (AspisR1.RoundPairing.dualFold alpha1
            (AspisR1.RoundPairing.dualFold alpha0
              (embeddedRow iota (raw k)))) := by
  let L0 := dualFoldLinear (n := 256) alpha0
  let L1 := dualFoldLinear (n := 64) alpha1
  let D := (dotLinear f).comp (L1.comp L0)
  change D (AspisR1.FunctionalWeights.weights
      (AspisR1.RawFunctionalWeights.rawFunctionals iota raw)
      (AspisR1.RawFunctionalWeights.rawBaseFunctional iota raw) kappa) = _
  rw [weights_eq_sum_embedded_rows]
  simp only [map_sum, map_smul, smul_eq_mul]
  rfl

#print axioms dualFoldLinear
#print axioms dotLinear
#print axioms weights_eq_sum_embedded_rows
#print axioms two_dual_dot_eq_seven_rows
end AspisR1.RawPairing
end

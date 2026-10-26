import R1FunctionalWeights

/-! Materialize six functional rows and one base row from raw `K`-valued
coefficient vectors. This is a finite-dimensional algebra identity only; it
does not identify `raw` with any Rust constructor or semantic functional. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawFunctionalWeights

open scoped BigOperators
variable {K E : Type} [Field K] [Field E]

/-- Embed a raw coefficient row and evaluate it as an `E`-linear functional. -/
def rowMap {n : Nat} (iota : K →+* E) (w : Fin n → K) :
    (Fin n → E) →ₗ[E] E where
  toFun m := ∑ i : Fin n, m i * iota (w i)
  map_add' x y := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [RingHom.id_apply]
    ring

theorem rowMap_single {n : Nat} (iota : K →+* E) (w : Fin n → K)
    (i : Fin n) : rowMap iota w (Pi.single i (1 : E)) = iota (w i) := by
  classical
  change (∑ j : Fin n,
    ((Pi.single i (1 : E) : Fin n → E) j) * iota (w j)) = _
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_apply]
  · intro j hj hji
    simp [Pi.single_apply, hji]
  · intro hnot
    exact (hnot (Finset.mem_univ i)).elim

/-- The six nonconstant functionals are rows 1 through 6 of `raw`. -/
def rawFunctionals {n : Nat} (iota : K →+* E)
    (raw : Fin 7 → Fin n → K) :
    Fin 6 → (Fin n → E) →ₗ[E] E :=
  fun j => rowMap iota (raw ⟨j.val + 1, by omega⟩)

/-- The constant functional is row 0 of `raw`. -/
def rawBaseFunctional {n : Nat} (iota : K →+* E)
    (raw : Fin 7 → Fin n → K) : (Fin n → E) →ₗ[E] E :=
  rowMap iota (raw 0)

theorem weights_eq_raw_rows {n : Nat} (iota : K →+* E)
    (raw : Fin 7 → Fin n → K) (kappa : E) (i : Fin n) :
    AspisR1.FunctionalWeights.weights
        (rawFunctionals iota raw) (rawBaseFunctional iota raw) kappa i =
      ∑ k : Fin 7, kappa ^ k.val * iota (raw k i) := by
  simp [AspisR1.FunctionalWeights.weights,
    AspisR1.FunctionalWeights.weightedMap, rawFunctionals,
    rawBaseFunctional, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, rowMap_single, Fin.sum_univ_succ]

/-- `rowMap` is exactly the ordinary coefficient dot product after embedding. -/
theorem rowMap_eq_dot {n : Nat} (iota : K →+* E) (w : Fin n → K)
    (m : Fin n → E) :
    rowMap iota w m = AspisR1.RoundPairing.dot m (fun i => iota (w i)) := rfl

#print axioms rowMap_single
#print axioms weights_eq_raw_rows
#print axioms rowMap_eq_dot
end AspisR1.RawFunctionalWeights
end

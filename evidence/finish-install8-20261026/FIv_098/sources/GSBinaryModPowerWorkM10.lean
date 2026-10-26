import CompPolyPolynomialBackendBridge
import ActualCompPolyPowCost

/-! The GS backend uses square-then-multiply followed by one remainder, not
Raw.powModWith's accumulator/current schedule. This mirror retains the exact
binaryRec schedule and counts both polynomial multiplications even on a zero
bit (the second multiplication is by one). Constants are protocol exponents,
not represented field values. -/
set_option autoImplicit false
namespace AspisR1.GSBinaryModPowerWorkM10
open CompPoly
variable {K : Type} [Field K] [BEq K] [LawfulBEq K]

def modPower (a m : CPolynomial K) : Nat → CPolynomial K × Nat :=
  Nat.binaryRec (1, 0) (fun b _ z =>
    ((z.1*z.1*(if b then a else 1)).modByMonic m, z.2+2))

theorem value (a m : CPolynomial K) (e : Nat) :
    (modPower a m e).1 = CompPolyPolynomialBackendBridge.modPower a m e := by
  refine Nat.binaryRec (motive := fun n =>
    (modPower a m n).1 = CompPolyPolynomialBackendBridge.modPower a m n) ?_ ?_ e
  · simp only [modPower, CompPolyPolynomialBackendBridge.modPower, Nat.binaryRec_zero]
  · intro b n ih
    by_cases hz : Nat.bit b n = 0
    · rw [hz]
      simp only [modPower, CompPolyPolynomialBackendBridge.modPower, Nat.binaryRec_zero]
    · have hc : n = 0 → b = true := by
        intro hn
        subst n
        cases b with
        | false => exact False.elim (hz rfl)
        | true => rfl
      unfold modPower CompPolyPolynomialBackendBridge.modPower
      rw [Nat.binaryRec_eq b n (Or.inr hc), Nat.binaryRec_eq b n (Or.inr hc)]
      change ((modPower a m n).1 * (modPower a m n).1 * (if b then a else 1)).modByMonic m = _
      rw [ih]
      rfl

theorem work (a m : CPolynomial K) (e : Nat) : (modPower a m e).2 ≤ 2*e := by
  refine Nat.binaryRec (motive := fun n => (modPower a m n).2 ≤ 2*n) ?_ ?_ e
  · simp only [modPower, Nat.binaryRec_zero, Nat.mul_zero, Nat.le_refl]
  · intro b n ih
    by_cases hz : Nat.bit b n = 0
    · rw [hz]
      simp only [modPower, Nat.binaryRec_zero, Nat.mul_zero, Nat.le_refl]
    · have hc : n = 0 → b = true := by
        intro hn
        subst n
        cases b with
        | false => exact False.elim (hz rfl)
        | true => rfl
      unfold modPower
      rw [Nat.binaryRec_eq b n (Or.inr hc)]
      change (modPower a m n).2+2 ≤ 2*Nat.bit b n
      cases b <;> simp only [Nat.bit_false, Nat.bit_true] at * <;> omega

/-- A small symbolic schedule counterexample: both computations have the
same fixed exponent, but the retained Raw power counter counts three calls
where the GS backend executes four polynomial multiplications. It is not a
value-inequality or a counterexample to the common 2*bitLength upper bound. -/
theorem gs_two (a m : CPolynomial K) : (modPower a m 2).2 = 4 := rfl

theorem raw_two (M : CPolynomial.Raw.MulContext K) (D : CPolynomial.Raw.ModContext K)
    (m a : CPolynomial.Raw K) : (ExtractorPowComplexity.powModWithCost M D m a 2).2 = 3 := by
  simp [ExtractorPowComplexity.powModWithCost, ExtractorPowComplexity.rawPowModWithCost]

theorem different_counter (a m : CPolynomial K)
    (M : CPolynomial.Raw.MulContext K) (D : CPolynomial.Raw.ModContext K) :
    (modPower a m 2).2 ≠ (ExtractorPowComplexity.powModWithCost M D m.val a.val 2).2 := by
  rw [gs_two, raw_two]
  decide

#print axioms value
#print axioms work
#print axioms gs_two
#print axioms raw_two
#print axioms different_counter
end AspisR1.GSBinaryModPowerWorkM10
